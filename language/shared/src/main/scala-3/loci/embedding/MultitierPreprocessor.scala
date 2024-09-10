package loci
package embedding

import impl.SymbolMutator
import utility.noReporting

import java.lang.reflect.Field
import java.util.IdentityHashMap
import scala.quoted.*
import scala.util.control.NonFatal

final class MultitierPreprocessor

object MultitierPreprocessor:
  transparent inline given MultitierPreprocessor = ${ preprocess }

  private inline val propagateTypesForPlacementCompounds = true
  private inline val insertNonplacedArgumentForValuesWithParams = true
  private inline val insertNonplacedReturnTypeForValuesWithoutParams = true
  private inline val insertComileTimeOnlyForPlacedValues = false
  private inline val repreprocessNestedMultitierModules = false

  val illegalPlacedValueAccessMessage =
    "Access to abstraction only allowed on peers on which the abstraction is placed. Remote access must be explicit."
  val illegalObjectMemberAccessMessage =
    "Access to object member of multitier module not allowed."

  def preprocess(using Quotes): Expr[MultitierPreprocessor] =
    import quotes.reflect.*

    val `language.on` = Symbol.requiredPackage("loci.language").typeMember("on")
    val `embedding.on` = Symbol.requiredPackage("loci.embedding").typeMember("on")
    val `embedding.of` = Symbol.requiredPackage("loci.embedding").typeMember("of")
    val `language.multitier` = Symbol.requiredClass("loci.language.multitier")
    val `embedding.multitier` = Symbol.requiredClass("loci.embedding.multitier")
    val nonplaced = Symbol.requiredClass("loci.embedding.Multitier.nonplaced")
    val `type` = Symbol.requiredModule("loci.embedding.Multitier").typeMember("type")
    val `Placed.Context` = Symbol.requiredClass("loci.embedding.On.Placed.Context")
    val peer = Symbol.requiredClass("loci.language.peer")
    val deferred = Symbol.requiredClass("loci.language.deferred")
    val placed = Symbol.requiredMethod("loci.language.placed.apply")
    val and = Symbol.requiredMethod("loci.language.and")
    val erased = (Symbol.requiredPackage("loci.embedding").methodMember("erased") find { _.paramSymss.sizeIs == 1 }).get
    val compileTimeOnly = Symbol.requiredClass("scala.annotation.compileTimeOnly")
    val uninitialized = Symbol.requiredMethod("scala.compiletime.uninitialized")

    def scopeSymbol(symbol: Symbol): Boolean =
      symbol.isValDef || symbol.isDefDef || symbol.isClassDef

    def scopeOwner(symbol: Symbol): Symbol =
      if symbol.exists && (symbol.isLocalDummy || !scopeSymbol(symbol)) then
        scopeOwner(symbol.owner)
      else
        symbol

    val owner =
      if Symbol.spliceOwner.flags is Flags.Macro then
        scopeOwner(Symbol.spliceOwner.owner)
      else
        scopeOwner(Symbol.spliceOwner)

    if owner.exists then
      try
        val flagsClass = Flags.EmptyFlags.getClass
        val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
        val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
        val symbolClass = Class.forName("dotty.tools.dotc.core.Symbols$Symbol")
        val symDenotationClass = Class.forName("dotty.tools.dotc.core.SymDenotations$SymDenotation")
        val annotationClass = Class.forName("dotty.tools.dotc.core.Annotations$Annotation")
        val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")
        val wildcardTypeClass = Class.forName("dotty.tools.dotc.core.Types$WildcardType$")
        val typerClass = Class.forName("dotty.tools.dotc.typer.Typer")
        val completerClass = Class.forName("dotty.tools.dotc.typer.Namer$Completer")
        val sourceFileClass = Class.forName("dotty.tools.dotc.util.SourceFile")
        val sourcePositionClass = Class.forName("dotty.tools.dotc.util.SourcePosition")
        val positionedClass = Class.forName("dotty.tools.dotc.ast.Positioned")
        val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
        val namesClass = Class.forName("dotty.tools.dotc.core.Names")
        val termNameClass = Class.forName("dotty.tools.dotc.core.Names$TermName")
        val applyKindClass = Class.forName("dotty.tools.dotc.ast.Trees$ApplyKind")
        val applyClass = Class.forName("dotty.tools.dotc.ast.Trees$Apply")
        val typeApplyClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeApply")
        val selectClass = Class.forName("dotty.tools.dotc.ast.Trees$Select")
        val identClass = Class.forName("dotty.tools.dotc.ast.Trees$Ident")
        val defTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$DefTree")
        val typeTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeTree")
        val blockClass = Class.forName("dotty.tools.dotc.ast.Trees$Block")
        val templateClass = Class.forName("dotty.tools.dotc.ast.Trees$Template")
        val valOrDefDefClass = Class.forName("dotty.tools.dotc.ast.Trees$ValOrDefDef")
        val valDefClass = Class.forName("dotty.tools.dotc.ast.Trees$ValDef")
        val defDefClass = Class.forName("dotty.tools.dotc.ast.Trees$DefDef")
        val typeDefClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeDef")
        val typeBoundsTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeBoundsTree")
        val refinedTypeTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$RefinedTypeTree")
        val appliedTypeTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$AppliedTypeTree")
        val untpdClass = Class.forName("dotty.tools.dotc.ast.untpd")
        val functionClass = Class.forName("dotty.tools.dotc.ast.untpd$Function")
        val moduleDefClass = Class.forName("dotty.tools.dotc.ast.untpd$ModuleDef")
        val infixOpClass = Class.forName("dotty.tools.dotc.ast.untpd$InfixOp")
        val typedSpliceClass = Class.forName("dotty.tools.dotc.ast.untpd$TypedSplice")
        val parensClass = Class.forName("dotty.tools.dotc.ast.untpd$Parens")
        val modifiersClass = Class.forName("dotty.tools.dotc.ast.untpd$Modifiers")

        val ctx = quotesImplClass.getMethod("ctx")
        val typer = contextClass.getMethod("typer")
        val denot = symbolClass.getMethod("denot", contextClass)
        val infoOrCompleter = symDenotationClass.getMethod("infoOrCompleter")
        val annotationsUnsafe = symDenotationClass.getMethod("annotationsUNSAFE", contextClass)
        val flagsUnsafe = symDenotationClass.getMethod("flagsUNSAFE")
        val resetFlag = symDenotationClass.getMethod("resetFlag", classOf[Long])
        val annotationSymbol = annotationClass.getMethod("symbol", contextClass)
        val wildcardType = wildcardTypeClass.getField("MODULE$")
        val typedType = typerClass.getMethod("typedType", treeClass, typeClass, classOf[Boolean], contextClass)
        val original = completerClass.getMethod("original")
        val contains = sourcePositionClass.getMethod("contains", sourcePositionClass)
        val sourcePos = positionedClass.getMethod("sourcePos", contextClass)
        val span = positionedClass.getMethod("span")
        val withSpan = positionedClass.getMethod("withSpan", classOf[Long])
        val isEmpty = treeClass.getMethod("isEmpty")
        val termName = namesClass.getMethod("termName", classOf[String])
        val apply = applyClass.getMethod("apply", treeClass, classOf[List[?]], sourceFileClass)
        val fun = applyClass.getMethod("fun")
        val setApplyKind = applyClass.getMethod("setApplyKind", applyKindClass)
        val typeApply = typeApplyClass.getMethod("apply", treeClass, classOf[List[?]], sourceFileClass)
        val nameSpan = selectClass.getMethod("nameSpan", contextClass)
        val rawMods = defTreeClass.getMethod("rawMods")
        val setMods = defTreeClass.getMethod("setMods", modifiersClass)
        val typeTree = typeTreeClass.getMethod("apply", sourceFileClass)
        val block = blockClass.getMethod("apply", classOf[List[?]], treeClass, sourceFileClass)
        val stats = blockClass.getMethod("stats")
        val expr = blockClass.getMethod("expr")
        val unforcedBody = templateClass.getMethod("unforcedBody")
        val name = valOrDefDefClass.getMethod("name")
        val valOrDefTpt = valOrDefDefClass.getMethod("tpt")
        val unforcedRhs = valOrDefDefClass.getMethod("unforcedRhs")
        val withFlags = valOrDefDefClass.getMethod("withFlags", classOf[Long])
        val valDef = valDefClass.getMethod("apply", termNameClass, treeClass, classOf[Object], sourceFileClass)
        val valTpt = valDefClass.getDeclaredField("tpt")
        val valRhs = valDefClass.getDeclaredField("preRhs")
        val defTpt = defDefClass.getDeclaredField("tpt")
        val defRhs = defDefClass.getDeclaredField("preRhs")
        val paramss = defDefClass.getDeclaredField("paramss")
        val rhs = typeDefClass.getMethod("rhs")
        val lo = typeBoundsTreeClass.getMethod("lo")
        val hi = typeBoundsTreeClass.getMethod("hi")
        val alias = typeBoundsTreeClass.getMethod("alias")
        val tpt = refinedTypeTreeClass.getDeclaredField("tpt")
        val refinedTpt = refinedTypeTreeClass.getMethod("tpt")
        val appliedTypeTreeArgs = appliedTypeTreeClass.getDeclaredField("args")
        val appliedTypeTree = appliedTypeTreeClass.getMethod("apply", treeClass, classOf[List[?]], sourceFileClass)
        val function = functionClass.getMethod("apply", classOf[List[?]], treeClass, sourceFileClass)
        val impl = moduleDefClass.getMethod("impl")
        val infix = infixOpClass.getMethod("apply", treeClass, identClass, treeClass, sourceFileClass)
        val right = infixOpClass.getMethod("right")
        val op = infixOpClass.getMethod("op")
        val left = infixOpClass.getMethod("left")
        val infixLeft = infixOpClass.getDeclaredField("left")
        val typedSplice = typedSpliceClass.getMethod("apply", treeClass, classOf[Boolean], contextClass)
        val splice = typedSpliceClass.getMethod("splice")
        val forwardTo = parensClass.getMethod("forwardTo")
        val modFlags = modifiersClass.getMethod("flags")
        val modAnnotations = modifiersClass.getMethod("annotations")
        val modWithAnnotations = modifiersClass.getMethod("withAnnotations", classOf[List[?]])
        val modWithAddedAnnotation = modifiersClass.getMethod("withAddedAnnotation", treeClass)

        val applyKindUsing = applyKindClass.getMethod("valueOf", classOf[String]).invoke(null, "Using")
        val emptyTree = untpdClass.getMethod("EmptyTree").invoke(null)

        val context = ctx.invoke(quotes)
        val contextTyper = typer.invoke(context)

        object QuotesSymbol:
          def unapply(symbol: Any): Option[Symbol] = symbol match
            case symbol: Symbol @unchecked if symbolClass.isInstance(symbol) => Some(symbol)
            case _ => None

        object QuotesTree:
          def unapply(tree: Any): Option[Tree] = tree match
            case tree: Tree @unchecked if treeClass.isInstance(tree) => Some(tree)
            case _ => None

        def tryTypingTypeTree(tpt: TypeTree) =
          noReporting(context)(null, useExploringContext = false): context =>
            typedType.invoke(contextTyper, tpt, wildcardType.get(null), false, context) match
              case QuotesTree(tpt: TypeTree) => Some(tpt)
              case _ => None

        def correctlyTyped(tpe: TypeRepr) = tpe match
          case _: TermRef | _: TypeRef | _: ConstantType | _: SuperType | _: Refinement |
               _: AppliedType | _: AnnotatedType | _: AndType | _: OrType | _: MatchType |
               _: ByNameType | _: ParamRef | _: ThisType | _: RecursiveThis | _: RecursiveType |
               _: MethodType | _: PolyType | _: TypeLambda | _: MatchCase | _: TypeBounds | _: NoPrefix =>
            true
          case _ =>
            false

        def completerOriginalTree(symbol: Symbol) =
          val info = infoOrCompleter.invoke(denot.invoke(symbol, context))
          Option.when(completerClass.isInstance(info)) { original.invoke(info) }

        def declarationsOfSymbol(symbol: Symbol) =
          completerOriginalTree(symbol).fold(symbol.declarations)(declarationsOfTree)

        def declarationsOfTree(tree: Any) =
          val blockOrTemplate =
            if valOrDefDefClass.isInstance(tree) then Some(unforcedRhs.invoke(tree))
            else if typeDefClass.isInstance(tree) then Some(rhs.invoke(tree))
            else if moduleDefClass.isInstance(tree) then Some(impl.invoke(tree))
            else None
          val statements = blockOrTemplate map: blockOrTemplate =>
            if blockClass.isInstance(blockOrTemplate) then stats.invoke(blockOrTemplate)
            else if templateClass.isInstance(blockOrTemplate) then unforcedBody.invoke(blockOrTemplate)
            else List.empty
          statements match
            case Some(stats: List[?]) =>
              stats filter: stat =>
                valDefClass.isInstance(stat) ||
                defDefClass.isInstance(stat) ||
                typeDefClass.isInstance(stat) ||
                moduleDefClass.isInstance(stat)
            case _ =>
              List.empty

        def declarations(decl: Any) = decl match
          case QuotesSymbol(symbol) => declarationsOfSymbol(symbol)
          case _ => declarationsOfTree(decl)

        def annotationIndex(decl: Any)(predicate: Any => Boolean) = decl match
          case QuotesSymbol(symbol) => annotationsUnsafe.invoke(denot.invoke(symbol, context), context) match
            case annotations: List[?] => annotations indexWhere { annotation => predicate(annotationSymbol.invoke(annotation, context)) }
            case _ => -1
          case tree => modAnnotations.invoke(rawMods.invoke(tree)) match
            case trees: List[?] => trees indexWhere predicate
            case _ => -1

        def hasAnnotation(decl: Any)(predicate: Any => Boolean) =
          annotationIndex(decl)(predicate) >= 0

        def annotationSymbolIndex(decl: Any, annotationSymbol: Symbol) =
          val name = annotationSymbol.name
          annotationIndex(decl):
            case QuotesSymbol(symbol) =>
              symbol == annotationSymbol
            case tree if typedSpliceClass.isInstance(tree) => splice.invoke(tree) match
              case QuotesTree(Apply(Select(New(tpt), _), _)) => tpt.symbol == annotationSymbol
              case _ => false
            case QuotesTree(Apply(Select(New(tpt @ (TypeIdent(`name`) | TypeSelect(_, `name`))), _), _)) =>
              tryTypingTypeTree(tpt) exists: tpt =>
                correctlyTyped(tpt.tpe) && tpt.symbol == annotationSymbol
            case _ =>
              false

        def hasAnnotationSymbol(decl: Any, annotationSymbol: Symbol) =
          annotationSymbolIndex(decl, annotationSymbol) >= 0

        def flags(decl: Any) =
          val flags = decl match
            case QuotesSymbol(symbol) => flagsUnsafe.invoke(denot.invoke(symbol, context))
            case tree => modFlags.invoke(rawMods.invoke(tree))
          flags match
            case flags: Flags @unchecked if flagsClass.isInstance(flags) => flags
            case _ => Flags.EmptyFlags

        def mutateField(field: Field, obj: Any, value: Any) =
          try
            field.setAccessible(true)
            field.set(obj, value)
          catch
            case NonFatal(_) =>

        def placementType(tpe: TypeRepr) =
          correctlyTyped(tpe) && !(tpe =:= TypeRepr.of[Nothing]) &&
          (tpe.typeSymbol == `language.on` || tpe.typeSymbol == `embedding.on`)

        def nonPlacementType(tpe: TypeRepr) =
          correctlyTyped(tpe) && !(tpe =:= TypeRepr.of[Nothing]) &&
          tpe.typeSymbol == `type`

        def maybePlacementRelatedTerm(tree: Any) = tree match
          case QuotesTree(
              Ident("on") |
              Select(Ident("language"), "on") |
              Select(Select(Ident("loci"), "language"), "on") |
              Select(Select(Select(Ident("_root_"), "loci"), "language"), "on")) =>
            true
          case _ =>
            false

        def maybePlacementRelatedTypeConstructorTree(tree: Any) = tree match
          case QuotesTree(
              TypeIdent("on") |
              TypeSelect(Ident("language"), "on") |
              TypeSelect(Select(Ident("loci"), "language"), "on") |
              TypeSelect(Select(Select(Ident("_root_"), "loci"), "language"), "on") |
              TypeSelect(Ident("embedding"), "on") |
              TypeSelect(Select(Ident("loci"), "embedding"), "on") |
              TypeSelect(Select(Select(Ident("_root_"), "loci"), "embedding"), "on") |
              TypeIdent("type") |
              TypeSelect(Ident("Multitier"), "type") |
              TypeSelect(Select(Ident("embedding"), "Multitier"), "type") |
              TypeSelect(Select(Select(Ident("loci"), "embedding"), "Multitier"), "type") |
              TypeSelect(Select(Select(Select(Ident("_root_"), "loci"), "embedding"), "Multitier"), "type")) =>
            true
          case _ =>
            false

        def maybeRelatedPlacementTypeTree(tree: Any) = tree match
          case _ if infixOpClass.isInstance(tree) => maybePlacementRelatedTypeConstructorTree(op.invoke(tree))
          case QuotesTree(Applied(tpt, List(_, _))) => maybePlacementRelatedTypeConstructorTree(tpt)
          case _ => false

        def TypedSplice(tree: Tree) =
          typedSplice.invoke(null, tree, false, context)

        val placedValueCompileTimeOnlyAnnotation =
          New(TypeIdent(compileTimeOnly)).select(compileTimeOnly.primaryConstructor).appliedTo(Literal(StringConstant(illegalPlacedValueAccessMessage)))

        val objectMemberCompileTimeOnlyAnnotation =
          New(TypeIdent(compileTimeOnly)).select(compileTimeOnly.primaryConstructor).appliedTo(Literal(StringConstant(illegalObjectMemberAccessMessage)))

        val deferredAnnotation =
          New(TypeIdent(deferred)).select(deferred.primaryConstructor).appliedToNone

        val multitierAnnotation =
          New(TypeIdent(`embedding.multitier`)).select(`embedding.multitier`.primaryConstructor).appliedToNone

        val processedDeclarations = IdentityHashMap[Any, Any]

        def processSymbol(decl: Any, multitierAnnottee: Boolean, nestedInMultitierAnnottee: Boolean, compileTimeOnlyAnnotation: Option[Term], symbol: Symbol): Unit =
          if repreprocessNestedMultitierModules || !(processedDeclarations containsKey symbol) then
            processedDeclarations.put(symbol, symbol)

            if (symbol.isValDef || symbol.isDefDef || symbol.isTypeDef) &&
               !(flags(symbol) is Flags.Module) &&
               !symbol.isClassDef &&
               !symbol.isClassConstructor then
              // process the original untyped tree if it exists
              completerOriginalTree(symbol) foreach:
                processTree(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, _)

              if symbol.isValDef || symbol.isDefDef then
                // allow abstract values in objects
                if multitierAnnottee && (flags(decl) is Flags.Module) && (flags(symbol) is Flags.Deferred) then
                  resetFlag.invoke(denot.invoke(symbol, context), Flags.Deferred)
                  if !hasAnnotationSymbol(symbol, deferred) then
                    SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, deferredAnnotation)

                // insert compile-time-only annotation (possibly if configured)
                if !hasAnnotationSymbol(symbol, compileTimeOnly) then
                  compileTimeOnlyAnnotation foreach:
                    SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, _)

            // recurse into objects and nested multitier classes and traits
            else if symbol.isClassDef && (hasAnnotationSymbol(symbol, `language.multitier`) || (flags(symbol) is Flags.Module)) then
              processDeclarations(symbol, nestedInMultitierAnnottee || multitierAnnottee)
          end if
        end processSymbol

        def processTree(decl: Any, multitierAnnottee: Boolean, nestedInMultitierAnnottee: Boolean, compileTimeOnlyAnnotation: Option[Term], tree: Any): Unit =
          if repreprocessNestedMultitierModules || !(processedDeclarations containsKey tree) then
            processedDeclarations.put(tree, tree)

            // adapt ascribed placement type of from `Nothing on P` to `Nothing of P on P`,
            // adapt ascribed non-placement type of from `T` to `nonplaced type T` on parameterless values that are not multitier modules (if configured),
            // allow abstract values in objects,
            // propagate types for placement compounds and rewrite infix `and` to standard method invocation (if configured)
            // insert placed syntax for definitions with placement type (or all definitions if configured)
            // insert implicit context argument for definitions with arguments (if configured),
            // insert compile-time-only annotation (possibly if configured)
            if valOrDefDefClass.isInstance(tree) && !(flags(tree) is Flags.ParamAccessor) then
              val rhs = unforcedRhs.invoke(tree)

              val hasNoParams =
                if defDefClass.isInstance(tree) then
                  try
                    paramss.setAccessible(true)
                    paramss.get(tree) match
                      case paramss: List[?] => paramss.isEmpty
                      case _ => false
                  catch
                    case NonFatal(_) => false
                else
                  valDefClass.isInstance(tree)

              val untypedTpt = valOrDefTpt.invoke(tree)
              val maybeTypedTpt = untypedTpt match
                // The `tpt` of a `val` or a `def` is always a `TypeTree`,
                // i.e., `isType` is true and they are no type bounds
                case tpt: TypeTree @unchecked if hasNoParams || maybeRelatedPlacementTypeTree(tpt) => tryTypingTypeTree(tpt)
                case _ => None
              val typedTpt = maybeTypedTpt getOrElse Singleton(Literal(NullConstant()))

              val hasPlacementType = placementType(typedTpt.tpe)
              val hasNonPlacementType = nonPlacementType(typedTpt.tpe)

              def nonplacedType(arg: Any) =
                appliedTypeTree.invoke(null, TypedSplice(TypeIdent(`type`)), List(TypedSplice(TypeIdent(nonplaced)), arg), Position.ofMacroExpansion.sourceFile)

              def of(args: List[Any]) =
                appliedTypeTree.invoke(null, TypedSplice(TypeIdent(`embedding.of`)), args, Position.ofMacroExpansion.sourceFile)

              def isNothing(tpe: TypeRepr): Boolean = tpe match
                case _ if !correctlyTyped(tpe) || !(tpe <:< TypeRepr.of[Nothing]) => false
                case AnnotatedType(underlying, _) => isNothing(underlying)
                case AndType(left, right) => isNothing(left) || isNothing(right)
                case OrType(left, right) => isNothing(left) && isNothing(right)
                case Refinement(parent, name, _) => name != "on" && isNothing(parent)
                case _ => tpe.typeSymbol != `embedding.of`

              // adapt ascribed placement type of from `Nothing on P` to `Nothing of P on P` and
              // adapt ascribed non-placement type of from `T` to `nonplaced type T` on parameterless values that are not multitier modules (if configured)
              (untypedTpt, typedTpt.tpe) match
                case (_, AppliedType(_, List(valueType, _)))
                    if hasPlacementType && isNothing(valueType) && infixOpClass.isInstance(untypedTpt) =>
                  mutateField(infixLeft, untypedTpt, of(List(left.invoke(untypedTpt), right.invoke(untypedTpt))))
                case (QuotesTree(Applied(tpt, args @ List(_, _))), AppliedType(_, List(valueType, _)))
                    if hasPlacementType && isNothing(valueType) =>
                  mutateField(appliedTypeTreeArgs, untypedTpt, of(args) :: args.tail)
                case (tpt, tpe) =>
                  def isMultitierModule =
                    hasAnnotationSymbol(tree, `language.multitier`) ||
                    (tpe.baseClasses exists: symbol =>
                      symbol.hasAnnotation(`language.multitier`) || symbol.hasAnnotation(`embedding.multitier`))
                  if insertNonplacedReturnTypeForValuesWithoutParams &&
                     multitierAnnottee &&
                     !hasNonPlacementType &&
                     !hasPlacementType &&
                     hasNoParams &&
                     isEmpty.invoke(tpt) == false &&
                     !isMultitierModule then
                    if valDefClass.isInstance(tree) then
                      mutateField(valTpt, tree, nonplacedType(tpt))
                    if defDefClass.isInstance(tree) then
                      mutateField(defTpt, tree, nonplacedType(tpt))

              if multitierAnnottee then
                // allow abstract values in objects
                if isEmpty.invoke(rhs) == true then
                  if flags(decl) is Flags.Module then
                    if !hasAnnotationSymbol(tree, deferred) then
                      setMods.invoke(tree, modWithAddedAnnotation.invoke(rawMods.invoke(tree), TypedSplice(deferredAnnotation)))
                    if valDefClass.isInstance(tree) then
                      mutateField(valRhs, tree, TypedSplice(Ref(uninitialized)))
                    if defDefClass.isInstance(tree) then
                      mutateField(defRhs, tree, TypedSplice(Ref(uninitialized)))

                else
                  val positionSpan = span.invoke(tree)

                  // propagate types for placement compounds and rewrite infix `and` to standard method invocation (if configured)
                  val adaptedRhs =
                    if propagateTypesForPlacementCompounds && hasPlacementType then
                      val markerName = termName.invoke(null, "<placement compound types propagated>")
                      val markerTree = TypedSplice(Literal(BooleanConstant(true)))
                      val markerDef =
                        withSpan.invoke(
                          withFlags.invoke(
                            valDef.invoke(null, markerName, TypedSplice(TypeTree.of[Boolean]), markerTree, Position.ofMacroExpansion.sourceFile),
                            Flags.Synthetic),
                          positionSpan)

                      def blockWithMarkerDef(tree: Any) =
                        block.invoke(null, List(markerDef), tree, Position.ofMacroExpansion.sourceFile)

                      val placementType = untypedTpt match
                        case _ if infixOpClass.isInstance(untypedTpt) => Some(left.invoke(untypedTpt) -> right.invoke(untypedTpt))
                        case QuotesTree(Applied(tpt, args @ List(left, right))) => Some(left -> right)
                        case _ => None

                      placementType.fold(rhs): (value, peer) =>
                        def adapt(span: Any, left: Any, right: Any): Option[(AnyRef, Option[Any])] =
                          propagate(left) flatMap: (left, leftPeer) =>
                            propagate(right) map: (right, rightPeer) =>
                              val leftTypeApply = typeApply.invoke(null, TypedSplice(Ref(and)), List(TypedSplice(TypeIdent(`embedding.on`)), value, leftPeer getOrElse peer), Position.ofMacroExpansion.sourceFile)
                              val leftApply = apply.invoke(null, leftTypeApply, List(left), Position.ofMacroExpansion.sourceFile)
                              val rightTypeApply = typeApply.invoke(null, leftApply, List(value, value, rightPeer getOrElse peer, peer), Position.ofMacroExpansion.sourceFile)
                              val rightApply = apply.invoke(null, rightTypeApply, List(right), Position.ofMacroExpansion.sourceFile)
                              (withSpan.invoke(rightApply, span), None)

                        def underlying(tree: Any): Any =
                          if parensClass.isInstance(tree) then underlying(forwardTo.invoke(tree)) else tree

                        def propagate(tree: Any): Option[(AnyRef, Option[Any])] = underlying(tree) match
                          case tree if infixOpClass.isInstance(tree) => (left.invoke(tree), op.invoke(tree), right.invoke(tree)) match
                            case (left, QuotesTree(op @ Ident("and")), right) =>
                              adapt(span.invoke(op), left, right)
                            case (QuotesTree(left @ TypeApply(fun, List(arg))), QuotesTree(op @ Ident("apply" | "local" | "sbj")), right) if maybePlacementRelatedTerm(fun) =>
                              val tree = infix.invoke(null, left, op, blockWithMarkerDef(right), Position.ofMacroExpansion.sourceFile)
                              Some(tree, Some(arg))
                            case _ =>
                              None
                          case QuotesTree(Apply(tree @ Select(left, "and"), List(right))) =>
                            adapt(nameSpan.invoke(tree, context), left, right)
                          case QuotesTree(Apply(term @ TypeApply(fun, List(arg)), List(expr))) if maybePlacementRelatedTerm(fun) =>
                            val tree = apply.invoke(null, term, List(blockWithMarkerDef(expr)), Position.ofMacroExpansion.sourceFile)
                            Some(tree, Some(arg))
                          case _ =>
                            None

                        propagate(rhs).fold(rhs) { (tree, _) => tree }
                    else
                      rhs
                  end adaptedRhs

                  // insert placed syntax for definitions with placement type (or all definitions if configured)
                  val placedRhs =
                    val rhsMutatedToPlacedConstruct =
                      if applyClass.isInstance(rhs) && applyClass.isInstance(fun.invoke(rhs)) then
                        val tree = fun.invoke(fun.invoke(rhs))
                        if typedSpliceClass.isInstance(tree) then
                          splice.invoke(tree) match
                            case QuotesTree(tree) => tree.symbol == placed
                            case _ => false
                        else
                          false
                      else
                        false

                    if (insertNonplacedReturnTypeForValuesWithoutParams || hasPlacementType) && !rhsMutatedToPlacedConstruct then
                      val contextSymbol = Symbol.newVal(Symbol.spliceOwner, "<synthetic context>", `Placed.Context`.typeRef, Flags.Synthetic, Symbol.noSymbol)
                      val contextTree = Block(List(ValDef(contextSymbol, Some(Ref(erased).appliedToType(TypeRepr.of[Nothing])))), Ref(contextSymbol))

                      val placedContext = setApplyKind.invoke(
                        apply.invoke(null, TypedSplice(Ref(placed)), List(TypedSplice(contextTree)), Position.ofMacroExpansion.sourceFile),
                        applyKindUsing)

                      val paramName = termName.invoke(null, "<synthetic context>")
                      val paramTypeTree = typeTree.invoke(null, Position.ofMacroExpansion.sourceFile)

                      val paramDef =
                        withSpan.invoke(
                          withFlags.invoke(
                            valDef.invoke(null, paramName, paramTypeTree, emptyTree, Position.ofMacroExpansion.sourceFile),
                            Flags.Synthetic | Flags.Param | Flags.Given),
                          positionSpan)


                      val contextFunction = function.invoke(null, List(paramDef), adaptedRhs, Position.ofMacroExpansion.sourceFile)

                      // extend the span of the right-hand-side macro application to the entire definition
                      // we use this extended span to identify the outer-most macro application when inferring context closures
                      withSpan.invoke(
                        apply.invoke(null, placedContext, List(contextFunction), Position.ofMacroExpansion.sourceFile),
                        positionSpan)
                    else
                      adaptedRhs
                  end placedRhs

                  if placedRhs ne rhs then
                    if valDefClass.isInstance(tree) then
                      mutateField(valRhs, tree, placedRhs)
                    if defDefClass.isInstance(tree) then
                      mutateField(defRhs, tree, placedRhs)
                end if

                // insert implicit context argument for definitions with arguments (if configured)
                if insertNonplacedArgumentForValuesWithParams && defDefClass.isInstance(tree) && !(flags(tree) is Flags.FieldAccessor) then
                  paramss.setAccessible(true)
                  paramss.get(tree) match
                    case paramClauses: List[?] if paramClauses.nonEmpty =>
                      val paramClausesMutatedToContextArgument =
                        paramClauses.last match
                          case List(param) if valDefClass.isInstance(param) =>
                            val tpt = valOrDefTpt.invoke(param)
                            if typedSpliceClass.isInstance(tpt) then
                              splice.invoke(tpt) match
                                case QuotesTree(tpt: TypeTree) => tpt.tpe == TypeRepr.of[Multitier.Context]
                                case _ => false
                            else
                              false
                          case _ =>
                            false

                      if !paramClausesMutatedToContextArgument then
                        val names = paramClauses flatMap:
                          case paramClause: List[?] =>
                            paramClause collect:
                              case param if valDefClass.isInstance(param) =>
                                name.invoke(param).toString
                          case _ =>
                            List.empty

                        def freshName(i: Int): String =
                          val name = s"x$$$i"
                          if names contains name then freshName(i + 1) else name

                        val paramName = termName.invoke(null, freshName(names.length + 1))
                        val paramTypeTree = TypedSplice(TypeTree.of[Multitier.Context])

                        val paramDef =
                          withSpan.invoke(
                            withFlags.invoke(
                              valDef.invoke(null, paramName, paramTypeTree, emptyTree, Position.ofMacroExpansion.sourceFile),
                              Flags.Synthetic | Flags.Param | Flags.Given),
                            span.invoke(tree))

                        paramss.set(tree, paramClauses :+ List(paramDef))
                      end if
                    case _ =>
                end if
              end if

              // insert compile-time-only annotation (possibly if configured)
              if !hasAnnotationSymbol(tree, compileTimeOnly) then
                compileTimeOnlyAnnotation foreach: compileTimeOnlyAnnotation =>
                  setMods.invoke(tree, modWithAddedAnnotation.invoke(rawMods.invoke(tree), TypedSplice(compileTimeOnlyAnnotation)))

            // make peer types refine `Any` instead of `AnyRef` (which is the default for refined types)
            else if typeDefClass.isInstance(tree) &&
                    typeBoundsTreeClass.isInstance(rhs.invoke(tree)) &&
                    hasAnnotationSymbol(tree, peer) then
              def adaptRefinement(tree: Any): Unit =
                if refinedTypeTreeClass.isInstance(tree) then
                  val tptTree = refinedTpt.invoke(tree)
                  if isEmpty.invoke(tptTree) == true then
                    mutateField(tpt, tree, TypedSplice(TypeTree.of[Any]))
                  else
                    adaptRefinement(tptTree)
              val rhsTree = rhs.invoke(tree)
              adaptRefinement(lo.invoke(rhsTree))
              adaptRefinement(hi.invoke(rhsTree))
              adaptRefinement(alias.invoke(rhsTree))

            // recurse into objects and nested multitier classes and traits
            else
              val isModuleDef = moduleDefClass.isInstance(tree)
              val isClassDef = typeDefClass.isInstance(tree) && templateClass.isInstance(rhs.invoke(tree))
              val index = if isModuleDef || isClassDef then annotationSymbolIndex(tree, `language.multitier`) else -1

              if isModuleDef && index >= 0 && nestedInMultitierAnnottee && !repreprocessNestedMultitierModules then
                val mods = rawMods.invoke(tree)
                modAnnotations.invoke(mods) match
                  case annotations: List[?] =>
                    setMods.invoke(tree, modWithAnnotations.invoke(mods, annotations.updated(index, TypedSplice(multitierAnnotation))))
                  case _ =>

              if isModuleDef || (isClassDef && index >= 0) then
                processDeclarations(tree, nestedInMultitierAnnottee || multitierAnnottee)
          end if
        end processTree

        def processDeclarations(decl: Any, nestedInMultitierAnnottee: Boolean): Unit =
          val multitierAnnottee = hasAnnotationSymbol(decl, `language.multitier`)
          val compileTimeOnlyAnnotation =
            if !multitierAnnottee then
              Some(objectMemberCompileTimeOnlyAnnotation)
            else if insertComileTimeOnlyForPlacedValues then
              Some(placedValueCompileTimeOnlyAnnotation)
            else
              None

          declarations(decl) foreach:
            case QuotesSymbol(symbol) => processSymbol(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, symbol)
            case tree => processTree(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, tree)
        end processDeclarations

        declarations(owner) foreach: decl =>
          if hasAnnotationSymbol(decl, `language.multitier`) then
            processDeclarations(decl, nestedInMultitierAnnottee = false)

      catch
        case NonFatal(e) =>

    '{ MultitierPreprocessor() }
  end preprocess
end MultitierPreprocessor
