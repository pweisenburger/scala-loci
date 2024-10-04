package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import java.lang.reflect.Array
import scala.annotation.experimental
import scala.util.control.NonFatal

@experimental
trait Checking:
  this: Component & Commons & ErrorReporter & Placements & NonPlacements & Peers & RemoteAccessorGeneration =>
  import quotes.reflect.*

  private val hasErrors =
    try
      val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
      val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
      val reporterClass = Class.forName("dotty.tools.dotc.reporting.Reporter")

      val ctx = quotesImplClass.getMethod("ctx")
      val reporter = contextClass.getMethod("reporter")
      val hasErrors = reporterClass.getMethod("hasErrors")

      () => hasErrors.invoke(reporter.invoke(ctx.invoke(quotes))) == true
    catch
      case NonFatal(_) =>
        () => false
  end hasErrors

  private val runRefChecks =
    try
      val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
      val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
      val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
      val megaPhaseClass = Class.forName("dotty.tools.dotc.transform.MegaPhase")
      val miniPhaseClass = Class.forName("dotty.tools.dotc.transform.MegaPhase$MiniPhase")
      val miniPhaseArrayClass = miniPhaseClass.arrayType()
      val elimRepeatedClass = Class.forName("dotty.tools.dotc.transform.ElimRepeated")
      val refChecksClass = Class.forName("dotty.tools.dotc.typer.RefChecks")

      val ctx = quotesImplClass.getMethod("ctx")
      val megaPhase = megaPhaseClass.getConstructor(miniPhaseArrayClass)
      val transformUnit = megaPhaseClass.getMethod("transformUnit", treeClass, contextClass)
      val runsAfter = miniPhaseClass.getMethod("runsAfter")
      val runsAfterGroupsOf = miniPhaseClass.getMethod("runsAfterGroupsOf")
      val elimRepeated = elimRepeatedClass.getConstructor()
      val refChecks = refChecksClass.getConstructor()

      val context = ctx.invoke(quotes)
      val elimRepeatedPhase = elimRepeated.newInstance()
      val refChecksPhase = refChecks.newInstance()

      if runsAfter.invoke(elimRepeatedPhase) == Set.empty &&
         runsAfterGroupsOf.invoke(elimRepeatedPhase) == Set.empty &&
         runsAfter.invoke(refChecksPhase) == Set("elimRepeated") &&
         runsAfterGroupsOf.invoke(refChecksPhase) == Set.empty then
        val miniPhases = Array.newInstance(miniPhaseClass, 2)
        Array.set(miniPhases, 0, elimRepeatedPhase)
        Array.set(miniPhases, 1, refChecksPhase)
        val phase = megaPhase.newInstance(miniPhases)
        (tree: Tree) => transformUnit.invoke(phase, tree, context)
      else
        (tree: Tree) => ()
    catch
      case NonFatal(_) =>
        (tree: Tree) => ()
  end runRefChecks

  private inline def treeType(tree: Tree) = tree match
    case tree: Term => tree.tpe
    case tree: TypeTree => tree.tpe
    case _ => TypeRepr.of[AnyRef]

  private def checkMultitierBaseTypes(bases: List[Tree]) =
    (bases find { base => treeType(base) =:= TypeRepr.of[AnyVal] }) orElse
    (bases find { base => treeType(base) <:< TypeRepr.of[AnyVal] }) foreach: base =>
      errorAndCancel(s"Multitier modules cannot extend ${prettyType("AnyVal")}.", base.posInUserCode)

    bases foreach: base =>
      treeType(base).baseClasses foreach: symbol =>
        if symbol != defn.AnyClass &&
           symbol != defn.AnyRefClass &&
           symbol != defn.ObjectClass &&
           symbol != defn.MatchableClass &&
           !isMultitierModule(symbol) &&
           (!(symbol.flags is Flags.NoInits) || symbol.declaredFields.nonEmpty || symbol.declaredMethods.nonEmpty) then
          errorAndCancel(s"Multitier modules cannot extend non-multitier modules: ${prettyType(symbol.typeRef.prettyShow)}", base.posInUserCode)
  end checkMultitierBaseTypes

  private object NestedApplies:
    def unapply(term: Term): Some[Term] = term match
      case Apply(NestedApplies(fun), _) => Some(fun)
      case _ => Some(term)

  private object multitierDefinitionsChecker extends TreeTraverser:
    override def traverseTree(tree: Tree)(owner: Symbol) =
      tree match
        case ValDef(_, tpt, rhs) if isMultitierModule(tree.symbol) && !tree.symbol.isModuleDef =>
          if tree.symbol.flags is Flags.Mutable then
            errorAndCancel("Multitier modules cannot be mutable variables.", tree.posInUserCode.firstCodeLine)
          else if tree.symbol.isParam then
            errorAndCancel("Multitier modules cannot be passed as parameters.", tree.posInUserCode.firstCodeLine)
          else
            val bases = tpt match
              case Inferred() =>
                List(tpt)
              case _=>
                def flatten(tpt: Tree): Option[List[Tree]] = tpt match
                  case Applied(andType, List(left, right)) if andType.symbol == symbols.`&` =>
                    flatten(left) flatMap { left => flatten(right) map { left ++ _ } }
                  case Applied(TypeIdent(_) | TypeSelect(_, _), _) | TypeIdent(_) | TypeSelect(_, _) =>
                    Some(List(tpt))
                  case _ =>
                    errorAndCancel("Unexpected type for multitier module.", tpt.posInUserCode)
                    None
                flatten(tpt).toList.flatten

            checkMultitierBaseTypes(bases)
            if bases forall { base => !isMultitierModule(treeType(base).typeSymbol) } then
              errorAndCancel("Type is not a multitier module.", tpt.posInUserCode)

            rhs match
              case _ if tree.symbol.hasAnnotation(symbols.deferred) =>
              case None =>
              case Some(rhs @ NestedApplies(Select(New(_), _))) if rhs.tpe.typeSymbol.flags is Flags.Final =>
                if !isMultitierModule(tree.symbol.owner) then
                  errorAndCancel(
                    "The implementation of a multitier module must be an `object`.",
                    tree.posInUserCode.firstCodeLine)
              case _ =>
                errorAndCancel(
                  "The implementation of a multitier module must be an `object` or the instantiation of a final class.",
                  tree.posInUserCode.firstCodeLine)

        case ValDef(_, tpt, _) if tree.symbol.isParam && !tree.symbol.owner.isFieldAccessor && PlacementInfo(tpt.tpe.widenByName).isDefined =>
          errorAndCancel("Placed values cannot be passed as parameters.", tree.posInUserCode.firstCodeLine)

        case ValDef(name, tpt, _) if tree.symbol.isField =>
          NonPlacementInfo(tpt.tpe.widenTermRefByName) foreach: nonPlacementInfo =>
            if nonPlacementInfo.valueType.baseClasses exists isMultitierModule then
              val annotateMessage =
                s"\nTry annotating the value explicitly: ${prettyAnnotation("@multitier")} ${prettyKeyword("val")} $name"
              val ascribeMessage = tpt match
                case Inferred() => s"\nAnd/or try ascribing the type explicitly: ${prettyKeyword("val")} $name: ${prettyType(nonPlacementInfo.valueType.prettyShow)}"
                case _ => ""
              errorAndCancel(s"Value was not inferred as multitier module.$annotateMessage$ascribeMessage", tree.posInUserCode.firstCodeLine)

        case DefDef(name, _, tpt, _) =>
          val tpe = NonPlacementInfo(tpt.tpe.widenTermRefByName).fold(tpt.tpe) { _.valueType }
          if tpe.baseClasses exists isMultitierModule then
            errorAndCancel(s"Multitier modules must be stable values: ${prettyKeyword("val")} $name", tree.posInUserCode.firstCodeLine)

        case _ =>

      super.traverseTree(tree)(owner)
  end multitierDefinitionsChecker

  private object multitierAnnotationChecker extends TreeTraverser:
    override def traverseTree(tree: Tree)(owner: Symbol) =
      tree match
        case ClassDef(_, _, _, _, _) if isMultitierModule(tree.symbol) =>
          val annotations = tree.symbol.annotations filter: term =>
            val symbol = term.tpe.typeSymbol
            symbol == symbols.`language.multitier` || symbol == symbols.`embedding.multitier`

          if annotations.sizeIs > 1 then
            errorAndCancel(s"Duplicate ${prettyAnnotation("@multitier")} annotation for multitier module.", tree.posInUserCode.firstCodeLine)
          else if annotations.isEmpty then
            report.warning(s"Multitier module should have a ${prettyAnnotation("@multitier")} annotation.", tree.posInUserCode.firstCodeLine)

        case _ =>

      super.traverseTree(tree)(owner)
  end multitierAnnotationChecker

  def checkMultitierAnnotations(module: ClassDef): Unit =
    multitierAnnotationChecker.traverseTree(module)(module.symbol.owner)

  def checkMultitierDefinitions(module: ClassDef): ClassDef =
    if module.symbol.flags is Flags.Case then
      val impl = if module.symbol.isModuleDef then "case objects" else "case classes"
      errorAndCancel(s"Multitier modules cannot be $impl.", module.posInUserCode.firstCodeLine)

    if !canceled then
      if module.symbol.flags is Flags.Trait then
        (module.parents find { parent => treeType(parent) =:= TypeRepr.of[Any] }) foreach: parent =>
          errorAndCancel("Multitier modules cannot be universal traits.", parent.posInUserCode)

      checkMultitierBaseTypes(module.parents)
    end if

    module.body foreach:
      case stat: Definition =>
        if (stat.name startsWith names.loci) ||
           ((stat.name startsWith s"<${names.placedValue}") ||
            (stat.name startsWith s"<${names.placedPrivateValue}") ||
            (stat.name startsWith s"<${names.placedStatement}") ||
            (stat.name startsWith s"<${names.placedValues}") ||
            (stat.name startsWith s"<${names.outerPlacedValues}")) &&
            (stat.name.lastOption contains '>') then
          errorAndCancel("Illegal name in multitier module.", stat.posInUserCode.firstCodeLine)
        else if stat.symbol.isParamAccessor then
          stat.symbol.info match
            case ByNameType(_) =>
            case tpe =>
              errorAndCancel(
                s"Arguments to multitier modules must be by-name: ${prettyType(s"=> ${tpe.prettyShowFrom(module.symbol)}")}",
                stat.posInUserCode.firstCodeLine)
        else if stat.symbol.flags is Flags.Inline then
          val impl = if stat.symbol.isMethod then "methods" else "values"
          errorAndCancel(s"Multitier modules cannot define inline $impl.", stat.posInUserCode.firstCodeLine)
      case _ =>

    multitierDefinitionsChecker.traverseTree(module)(module.symbol.owner)

    module.body foreach:
      case stat: TypeDef if stat.symbol.hasAnnotation(symbols.peer) =>
        PeerInfo.check(stat, shallow = true).left foreach errorAndCancel
      case _ =>

    if canceled then
      disableErrorAndCancel()

    module.body foreach:
      case stat: TypeDef if stat.symbol.hasAnnotation(symbols.peer) =>
        PeerInfo.check(stat).left foreach errorAndCancel
      case _ =>

    if canceled then
      disableErrorAndCancel()

    val result =
      if !canceled && !hasErrors() then
        val result = materializeDummySignatures(module)
        runRefChecks(result)
        result
      else
        module

    if hasErrors() then
      cancel()

    result
  end checkMultitierDefinitions

  def checkDeferredDefinitions(module: ClassDef): ClassDef =
    def body(term: Term): Term = term match
      case block @ Lambda(arg :: _, expr) if arg.symbol.isImplicit => expr
      case _ => term

    module.body foreach: stat =>
      val (rhs, deferred) = stat match
        case ValDef(_, _, rhs) if stat.symbol.hasAnnotation(symbols.deferred) => (rhs map body, true)
        case DefDef(_, _, _, rhs) if stat.symbol.hasAnnotation(symbols.deferred) => (rhs map body, true)
        case _ => (None, false)

      if deferred && rhs.isDefined && !(module.symbol.flags is Flags.Final) then
        errorAndCancel(
          s"Definitions with ${prettyAnnotation("@deferred")} annotation in non-final classes or traits must be abstract.",
          stat.posInUserCode.firstCodeLine)
      else
        if deferred && (stat.symbol.flags is Flags.Private) then
          errorAndCancel("Abstract value cannot have `private` modifier.", stat.posInUserCode.firstCodeLine)

        rhs foreach:
          case uninitialized @ (Ident(_) | Select(_, _))
            if uninitialized.symbol == symbols.uninitialized =>
          case Block(List(uninitialized @ (Ident(_) | Select(_, _))), erased: TypeApply)
            if uninitialized.symbol == symbols.uninitialized && (erased.symbol == symbols.erased || erased.symbol == symbols.erasedArgs) =>
          case rhs =>
            errorAndCancel(
              s"Definitions with ${prettyAnnotation("@deferred")} annotation in final classes or objects must be initialized with `scala.compiletime.uninitialized`.",
              stat.posInUserCode.firstCodeLine)

    module
  end checkDeferredDefinitions
end Checking
