package loci
package embedding

import impl.Cache
import impl.SymbolMutator
import utility.noReporting
import utility.reflectionExtensions.*

import java.util.IdentityHashMap
import scala.annotation.Annotation
import scala.collection.mutable
import scala.util.control.NonFatal
import scala.util.Try
import scala.quoted.*

final class MultitierPreprocessor

object MultitierPreprocessor:
  type Type[T] = T

  final class multitier extends Annotation:
    def this(v: multitier) = this()

  transparent inline given moduleArgument: MultitierPreprocessor = ${ moduleArgumentImpl }
  transparent inline def moduleDefinition: Any = ${ moduleDefinitionImpl }
  transparent inline def moduleAnnotation: Any = ${ moduleAnnotationImpl }
  transparent inline def memberAscription: Any = ${ memberAscriptionImpl }
  transparent inline def memberDefinition[T](inline body: T): T = ${ memberDefinitionImpl('body) }

  private inline val propagateTypesForPlacementCompounds = true
  private inline val insertNonplacedReturnTypeForValuesWithoutParams = true
  private inline val insertComileTimeOnlyForPlacedValues = false

  private val preprocessedCompilationUnits = mutable.WeakHashMap.empty[Any, Unit]
  private val preprocessorAnnotated = mutable.WeakHashMap.empty[Any, Unit]
  private val nonplacedMembers = mutable.WeakHashMap.empty[Any, Unit]

  private val annotationTypingContext = Cache[Any, Quotes]

  def annotationTypingContext(using Quotes)(symbol: quotes.reflect.Symbol): Option[Quotes] =
    annotationTypingContext.get(symbol)

  val illegalPlacedValueAccessMessage =
    "Access to abstraction only allowed on peers on which the abstraction is placed. Remote access must be explicit."
  val illegalObjectMemberAccessMessage =
    "Access to object member of multitier module not allowed."

  def moduleArgumentImpl(using Quotes): Expr[MultitierPreprocessor] =
    import quotes.reflect.*

    try
      val commons = Commons()
      val reflectionExtensions = ReflectionExtensions()

      import commons.*
      import reflectionExtensions.*

      val context = ctx.invoke(quotes)

      def lastSingletonSubList(list: List[?]): List[?] = list match
        case Nil => Nil
        case _ :: Nil => list
        case _ :: list => lastSingletonSubList(list)

      def maybeMultitierAnnotationTypeTree(tpt: TypeTree): Boolean = tpt match
        case
            TypeIdent("multitier") |
            TypeSelect(Ident("language"), "multitier") |
            TypeSelect(Select(Ident("loci"), "language"), "multitier") |
            TypeSelect(Select(Select(Ident("_root_"), "loci"), "language"), "multitier") =>
          true
        case _ =>
          false

      def maybeMultitierAnnotation(tree: Tree): Boolean = tree match
        case New(tpt) => maybeMultitierAnnotationTypeTree(tpt)
        case Apply(fun, _) => maybeMultitierAnnotation(fun)
        case TypeApply(fun, _) => maybeMultitierAnnotation(fun)
        case Select(qualifier, _) => maybeMultitierAnnotation(qualifier)
        case _ if typedSpliceClass.isInstance(tpt) => splice.invoke(tpt) match
          case QuotesTree(tree) => maybeMultitierAnnotation(tree)
          case _ => false

      def preprocessorAnnotation(using SpannedPosition) =
        UntypedApply(
          UntypedSelect(
            UntypedNew(UntypedSelect(UntypedSelect(TypedSplice(Ref(multitierPreprocessor)), termName("moduleDefinition")), typeName("multitier"))),
            termName("<init>")),
          List(
            UntypedApply(
              UntypedSelect(
                UntypedNew(UntypedSelect(UntypedSelect(TypedSplice(Ref(multitierPreprocessor)), termName("moduleAnnotation")), typeName("multitier"))),
                termName("<init>")),
              List.empty)))

      def hasPreprocessorAnnotation(decl: Any) =
        hasAnnotation(decl):
          case QuotesTree(Apply(Select(New(TypeSelect(Select(qualifier, "moduleDefinition"), "multitier")), "<init>"), _)) =>
            typedSpliceClass.isInstance(qualifier) && qualifier.symbol == multitierPreprocessor
          case _ =>
            false

      def processAnnotations(tree: Any, containsExpandingTree: Boolean): Unit =
        val isModuleDef = moduleDefClass.isInstance(tree)
        val isClassDef = typeDefClass.isInstance(tree) && templateClass.isInstance(rhs.invoke(tree))

        if isModuleDef || isClassDef then
          if !(preprocessorAnnotated contains tree) && !hasPreprocessorAnnotation(tree) then
            preprocessorAnnotated += tree -> ()

            val index = annotationIndex(tree):
              case QuotesTree(tree) =>
                maybeMultitierAnnotation(tree) || containsExpandingTree && contains.invoke(sourcePos.invoke(tree, context), Position.ofMacroExpansion) == true
              case _ =>
                false

            if index >= 0 then
              modAnnotations.invoke(rawMods.invoke(tree)) match
                case annotations: List[?] =>
                  annotations(index) match
                    case QuotesTree(Apply(fun, _)) =>
                      SpannedPosition(fun.pos.sourceFile, span.invoke(fun)):
                        lastSingletonSubList(annotations) match
                          case last @ _ :: _ => setNext(last, List(preprocessorAnnotation))
                          case _ =>
                    case _ =>
                case _ =>
        end if

        tree match
          case iterable: Iterable[?] => iterable foreach { processAnnotations(_, containsExpandingTree) }
          case product: Product => product.productIterator foreach { processAnnotations(_, containsExpandingTree) }
          case _ =>
      end processAnnotations

      val currentUnit = compilationUnit.invoke(ctx.invoke(quotes))

      units.invoke(run.invoke(ctx.invoke(quotes))) match
        case compilationUnits: List[?] =>
          compilationUnits foreach: unit =>
            if !(preprocessedCompilationUnits contains unit) || unit == currentUnit then
              preprocessedCompilationUnits += unit -> ()
              processAnnotations(untpdTree.invoke(unit), containsExpandingTree = unit == currentUnit)
        case _ =>

      macroAnnotteeDeclarations foreach:
        case QuotesSymbol(symbol) if !(preprocessorAnnotated contains symbol) =>
          annotationsUnsafe.invoke(denot.invoke(symbol, context), context) match
            case annotations: List[?] =>
              if annotations exists { isEvaluating.invoke(_) == true } then
                preprocessorAnnotated += symbol -> ()

                val tree =
                  SpannedPosition(Position.ofMacroExpansion):
                    preprocessorAnnotation

                def treeTyping(otherContext: Any) =
                  typedAheadExpr.invoke(typer.invoke(context), tree, wildcardType.get(null), context)

                val annotation =
                  lazyAnnotation.invoke(null, `multitierPreprocessor.multitier`, treeTyping)

                lastSingletonSubList(annotations) match
                  case last @ _ :: _ => setNext(last, List(annotation))
                  case _ =>
            case _ =>
        case _ =>

    catch
      case NonFatal(e) =>

    moduleDefinitionImpl

    '{ MultitierPreprocessor() }
  end moduleArgumentImpl

  def moduleDefinitionImpl(using Quotes): Expr[Any] =
    val commons = Commons()
    import commons.*
    import quotes.reflect.*

    try
      val reflectionExtensions = ReflectionExtensions()
      import reflectionExtensions.*

      val context = ctx.invoke(quotes)
      val processedDeclarations = IdentityHashMap[Any, Any]

      def processSymbol(decl: Any, multitierAnnottee: Boolean, nestedInMultitierAnnottee: Boolean, compileTimeOnlyAnnotation: Option[Term], symbol: Symbol): Unit =
        if !(processedDeclarations containsKey symbol) then
          processedDeclarations.put(symbol, symbol)

          if (symbol.isValDef || symbol.isDefDef || symbol.isTypeDef) &&
             !(flags(symbol) is Flags.Module) &&
             !symbol.isClassDef &&
             !symbol.isClassConstructor then
            val tree = completerOriginalTree(symbol)

            tree foreach:
              // process the original untyped tree if it exists
              processTree(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, _)

            if (symbol.isValDef || symbol.isDefDef) &&
               !(flags(symbol) is Flags.FieldAccessor) &&
               !(flags(symbol) is Flags.ParamAccessor) &&
               !(flags(symbol) is Flags.Inline) then
              // allow abstract values in objects
              if multitierAnnottee && (flags(decl) is Flags.Module) && (flags(symbol) is Flags.Deferred) then
                resetFlag.invoke(denot.invoke(symbol, context), Flags.Deferred)
                if !hasAnnotationSymbol(symbol, deferred) then
                  SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, deferredAnnotation)

              // insert compile-time-only annotation (possibly if configured)
              if !hasAnnotationSymbol(symbol, compileTimeOnly) then
                compileTimeOnlyAnnotation foreach:
                  SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, _)

            // make peer types refine `Any` instead of `AnyRef` (which is the default for refined types)
            else if multitierAnnottee && tree.isEmpty && symbol.isType && hasAnnotationSymbol(symbol, peer) then
              def adaptedRefinement(tpe: Refinement): Refinement = tpe match
                case Refinement(parent, name, info) if parent =:= TypeRepr.of[Object] => Refinement(TypeRepr.of[Any], name, info)
                case Refinement(parent: Refinement, name, info) => Refinement(adaptedRefinement(parent), name, info)
                case tpe => tpe
              val info =
                symbolInfo(symbol) match
                  case TypeBounds(low, hi: Refinement) => TypeBounds(low, adaptedRefinement(hi))
                  case tpe => tpe
              SymbolMutator.getOrErrorAndAbort.setInfo(symbol, info)

          else if symbol.isClassDef && !hasAnnotationSymbol(symbol, `language.multitier`) then
            // recurse into nested classes, traits and objects that are not multitier modules
            processDeclarations(symbol, nestedInMultitierAnnottee || multitierAnnottee)
        end if
      end processSymbol

      def processTree(decl: Any, multitierAnnottee: Boolean, nestedInMultitierAnnottee: Boolean, compileTimeOnlyAnnotation: Option[Term], tree: Any): Unit =
        if !(processedDeclarations containsKey tree) then
          processedDeclarations.put(tree, tree)

          // adapt the definition of values
          // - adapt ascribed placement type of from `Nothing on P` to `Nothing of P on P`
          // - adapt ascribed non-placement type of from `T` to `nonplaced type T` on parameterless values that are not multitier modules (if configured)
          // - allow abstract values in objects
          // - propagate types for placement compounds and rewrite infix `and` to standard method invocation (if configured)
          // - insert placed syntax for definitions with placement type (or all definitions if configured)
          // - insert compile-time-only annotation (possibly if configured)
          if multitierAnnottee &&
             valOrDefDefClass.isInstance(tree) &&
             !(flags(tree) is Flags.FieldAccessor) &&
             !(flags(tree) is Flags.ParamAccessor) &&
             !(flags(tree) is Flags.Inline) then
            valOrDefTpt.invoke(tree) match
              case QuotesTree(Applied(TypeSelect(Select(qualifier, "memberAscription"), "Type"), List(_))) if qualifier.symbol == multitierPreprocessor =>
              case tpt if isEmpty.invoke(tpt) == true =>
                adaptMemberDefinitionBody(tree, hasPlacementType = false)
              case tpt =>
                val memberAscription =
                  SpannedPosition(Position.ofMacroExpansion):
                    UntypedApplied(
                      UntypedSelect(
                        UntypedSelect(
                          TypedSplice(Ref(multitierPreprocessor)),
                          termName("memberAscription")),
                        typeName("Type")),
                      List(tpt))
                if valDefClass.isInstance(tree) then
                  valTpt.set(tree, memberAscription)
                if defDefClass.isInstance(tree) then
                  defTpt.set(tree, memberAscription)

            // insert compile-time-only annotation (possibly if configured)
            if !hasAnnotationSymbol(tree, compileTimeOnly) then
              compileTimeOnlyAnnotation foreach: compileTimeOnlyAnnotation =>
                setMods.invoke(tree, modWithAddedAnnotation.invoke(rawMods.invoke(tree), TypedSplice(compileTimeOnlyAnnotation)))

          // make peer types refine `Any` instead of `AnyRef` (which is the default for refined types)
          else if multitierAnnottee &&
                  typeDefClass.isInstance(tree) &&
                  typeBoundsTreeClass.isInstance(rhs.invoke(tree)) &&
                  hasAnnotationSymbol(tree, peer) then
            def adaptRefinement(tree: Any): Unit =
              if refinedTypeTreeClass.isInstance(tree) then
                val tptTree = tpt.invoke(tree)
                if isEmpty.invoke(tptTree) == true then
                  refinedTpt.set(tree, TypedSplice(TypeTree.of[Any]))
                else
                  adaptRefinement(tptTree)
            val rhsTree = rhs.invoke(tree)
            adaptRefinement(lo.invoke(rhsTree))
            adaptRefinement(hi.invoke(rhsTree))
            adaptRefinement(alias.invoke(rhsTree))

          // recurse into nested classes, traits and objects that are not multitier modules
          else
            val isModuleDef = moduleDefClass.isInstance(tree)
            val isClassDef = typeDefClass.isInstance(tree) && templateClass.isInstance(rhs.invoke(tree))
            if (isModuleDef || isClassDef) && !hasAnnotationSymbol(tree, `language.multitier`) then
              processDeclarations(tree, nestedInMultitierAnnottee || multitierAnnottee)
        end if
      end processTree

      def processDeclarations(decl: Any, nestedInMultitierAnnottee: Boolean): Unit =
        val multitierAnnottee = hasAnnotationSymbol(decl, `language.multitier`)

        if multitierAnnottee && !nestedInMultitierAnnottee then
          decl match
            case QuotesSymbol(symbol) if flags(symbol) is Flags.Trait | Flags.NoInits =>
              SymbolMutator.getOrErrorAndAbort.resetFlag(symbol, Flags.NoInits)
            case _ =>

        val compileTimeOnlyAnnotation =
          if !multitierAnnottee then
            Some(objectMemberCompileTimeOnlyAnnotation)
          else if insertComileTimeOnlyForPlacedValues then
            Some(placedValueCompileTimeOnlyAnnotation)
          else
            None

        if multitierAnnottee != nestedInMultitierAnnottee then
          declarations(decl) foreach:
            case QuotesSymbol(symbol) => processSymbol(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, symbol)
            case tree => processTree(decl, multitierAnnottee, nestedInMultitierAnnottee, compileTimeOnlyAnnotation, tree)
      end processDeclarations

      macroAnnotteeDeclarations foreach { processDeclarations(_, nestedInMultitierAnnottee = false) }

    catch
      case NonFatal(e) =>

    Ref(multitierPreprocessor).asExprOf[Any]
  end moduleDefinitionImpl

  def moduleAnnotationImpl(using Quotes): Expr[Any] =
    val commons = Commons()
    import commons.*
    import quotes.reflect.*

    try
      val reflectionExtensions = ReflectionExtensions()
      import reflectionExtensions.*

      val context = ctx.invoke(quotes)

      def isMultitierPreprocessorAnnotation(tree: Tree) =
        tree match
          case QuotesTree(Apply(Select(New(TypeSelect(Select(qualifier, "moduleDefinition"), "multitier")), "<init>"), _)) =>
            typedSpliceClass.isInstance(qualifier) && qualifier.symbol == multitierPreprocessor
          case _ =>
            isAnnotationTreeSymbol(tree, `multitierPreprocessor.multitier`)

      def dropMultitierPreprocessorAnnotationInList(annotations: List[?]): Unit =
        annotations match
          case annotations @ _ :: QuotesTree(head) :: tail if isMultitierPreprocessorAnnotation(head) =>
            setNext(annotations, tail)
            dropMultitierPreprocessorAnnotationInList(annotations)
          case _ :: tail =>
            dropMultitierPreprocessorAnnotationInList(tail)
          case _ =>

      def dropMultitierPreprocessorAnnotationOfTree(tree: Any): Unit =
        modAnnotations.invoke(rawMods.invoke(tree)) match
          case annotations: List[?] => dropMultitierPreprocessorAnnotationInList(annotations)
          case _ =>

      def dropMultitierPreprocessorAnnotationOfSymbol(symbol: Symbol): Unit =
        completerOriginalTree(symbol) foreach dropMultitierPreprocessorAnnotationOfTree
        SymbolMutator.getOrErrorAndAbort.removeAnnotation(symbol, `multitierPreprocessor.multitier`)

      def dropMultitierPreprocessorAnnotation(decl: Any): Unit =
        decl match
          case QuotesSymbol(symbol) => dropMultitierPreprocessorAnnotationOfSymbol(symbol)
          case _ => dropMultitierPreprocessorAnnotationOfTree(decl)

      macroAnnotteeDeclarations foreach: decl =>
        decl match
          case QuotesSymbol(symbol) =>
            if hasAnnotationSymbol(symbol, `language.multitier`) then
              annotationTypingContext.update(symbol, quotes)
          case _ =>

        dropMultitierPreprocessorAnnotation(decl)

    catch
      case NonFatal(e) =>

    Ref(multitierPreprocessor).asExprOf[Any]
  end moduleAnnotationImpl

  def memberAscriptionImpl(using Quotes): Expr[Any] =
    val commons = Commons()
    import commons.*
    import quotes.reflect.*

    try
      val reflectionExtensions = ReflectionExtensions()
      import reflectionExtensions.*

      val context = ctx.invoke(quotes)
      val owner = scopeOwner(Symbol.spliceOwner)

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

      completerOriginalTree(owner) foreach: tree =>
        if valOrDefDefClass.isInstance(tree) then
          val rhs = unforcedRhs.invoke(tree)

          val rhsMutatedToMemberDefinition =
            if applyClass.isInstance(rhs) && selectClass.isInstance(fun.invoke(rhs)) then
              val tree = qualifier.invoke(fun.invoke(rhs))
              if typedSpliceClass.isInstance(tree) then
                splice.invoke(tree) match
                  case QuotesTree(tree) => tree.symbol == multitierPreprocessor
                  case _ => false
              else
                false
            else
              false

          if !rhsMutatedToMemberDefinition then
            valOrDefTpt.invoke(tree) match
              case QuotesTree(Applied(TypeSelect(Select(qualifier, "memberAscription"), "Type"), List(untypedTpt))) if qualifier.symbol == multitierPreprocessor =>
                if valDefClass.isInstance(tree) then
                  valTpt.set(tree, untypedTpt)
                if defDefClass.isInstance(tree) then
                  defTpt.set(tree, untypedTpt)

                val hasParams =
                  if defDefClass.isInstance(tree) then
                    try
                      paramss.invoke(tree) match
                        case paramss: List[?] => paramss.nonEmpty
                        case _ => true
                    catch
                      case NonFatal(_) => true
                  else
                    !valDefClass.isInstance(tree)

                val maybeTypedTpt = untypedTpt match
                  // The `tpt` of a `val` or a `def` is always a `TypeTree`,
                  // i.e., `isType` is true and they are not type bounds
                  case tpt: TypeTree @unchecked if !hasParams || maybeRelatedPlacementTypeTree(tpt) => tryTypingTypeTree(tpt)
                  case _ => None
                val typedTpt = maybeTypedTpt getOrElse Singleton(Literal(NullConstant()))

                def maybeInstantiation(term: Term): Boolean = term match
                  case Apply(fun, _) => maybeInstantiation(fun)
                  case Select(qualifier, _) => maybeInstantiation(qualifier)
                  case Ident(_) | New(_) => true
                  case _ => false

                def rhsInstantiationTypeIfDeficientTpt =
                  val maybeTypedTerm = rhs match
                    // The `rhs` of a `val` or a `def` is always a `Term`
                    case rhs: Term @unchecked if (maybeTypedTpt forall { tpt => !correctlyTyped(tpt.tpe) }) && maybeInstantiation(rhs) => tryTypingTerm(rhs)
                    case _ => None
                  maybeTypedTerm.fold(ConstantType(NullConstant())) { _.tpe }

                val hasPlacementType = placementType(typedTpt.tpe)
                val hasNonPlacementType = nonPlacementType(typedTpt.tpe)

                def nonplacedType(arg: Any)(using SpannedPosition) =
                  UntypedApplied(TypedSplice(TypeIdent(`type`)), List(TypedSplice(TypeIdent(nonplaced)), arg))

                def of(args: List[Any])(using SpannedPosition) =
                  UntypedApplied(TypedSplice(TypeIdent(`embedding.of`)), args)

                // adapt ascribed placement type of from `Nothing on P` to `Nothing of P on P` and
                // adapt ascribed non-placement type of from `T` to `nonplaced type T` on parameterless values that are not multitier modules (if configured)
                val isMultitierModule =
                  SpannedPosition(Position.ofMacroExpansion.sourceFile, span.invoke(untypedTpt)):
                    (untypedTpt, typedTpt.tpe) match
                      case (_, AppliedType(_, List(valueType, _)))
                          if hasPlacementType && isNothing(valueType) && infixOpClass.isInstance(untypedTpt) =>
                        infixLeft.set(untypedTpt, of(List(left.invoke(untypedTpt), right.invoke(untypedTpt))))
                        false
                      case (QuotesTree(Applied(tpt, args @ List(_, _))), AppliedType(_, List(valueType, _)))
                          if hasPlacementType && isNothing(valueType) =>
                        appliedTypeTreeArgs.set(untypedTpt, of(args) :: args.tail)
                        false
                      case (tpt, tpe) =>
                        def isMultitierModule =
                          hasAnnotationSymbol(tree, `language.multitier`) ||
                          (tpe.baseClasses exists: symbol =>
                            symbol.hasAnnotation(`language.multitier`) || symbol.hasAnnotation(`embedding.multitier`)) ||
                          (rhsInstantiationTypeIfDeficientTpt.baseClasses exists: symbol =>
                            symbol.hasAnnotation(`language.multitier`) || symbol.hasAnnotation(`embedding.multitier`))
                        if insertNonplacedReturnTypeForValuesWithoutParams &&
                           !hasNonPlacementType &&
                           !hasPlacementType &&
                           isEmpty.invoke(tpt) == false &&
                           !isMultitierModule then
                          if valDefClass.isInstance(tree) then
                            nonplacedMembers += owner -> ()
                            valTpt.set(tree, nonplacedType(tpt))
                          if defDefClass.isInstance(tree) then
                            nonplacedMembers += owner -> ()
                            defTpt.set(tree, nonplacedType(tpt))
                        isMultitierModule

                val positionSpan =
                  if isEmpty.invoke(rhs) == false then
                    span.invoke(rhs)
                  else
                    span.invoke(tree)

                SpannedPosition(Position.ofMacroExpansion.sourceFile, positionSpan):
                  if isEmpty.invoke(rhs) == true then
                    // allow abstract values in objects
                    val isDeferred = hasAnnotationSymbol(tree, deferred)
                    if (flags(owner.maybeOwner) is Flags.Module) || (flags(owner.maybeOwner) is Flags.Final) && isDeferred then
                      if flags(owner) is Flags.Deferred then
                        resetFlag.invoke(denot.invoke(owner, context), Flags.Deferred)
                      if !isDeferred then
                        SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(owner, deferredAnnotation)
                      if valDefClass.isInstance(tree) then
                        valRhs.set(tree, TypedSplice(Ref(uninitialized)))
                      if defDefClass.isInstance(tree) then
                        defRhs.set(tree, TypedSplice(Ref(uninitialized)))
                    end if
                  else
                    adaptMemberDefinitionBody(tree, hasPlacementType)

                  val nonEmptyRhs =
                    val rhs = unforcedRhs.invoke(tree)
                    if isEmpty.invoke(rhs) == true then
                      TypedSplice(Ref(erased).appliedToType(TypeRepr.of[Nothing]))
                    else
                      rhs

                  val memberDefinitionRhs =
                    UntypedApply(
                      UntypedSelect(
                        TypedSplice(Ref(multitierPreprocessor)),
                        termName("memberDefinition")),
                      List(nonEmptyRhs))

                  if valDefClass.isInstance(tree) then
                    valRhs.set(tree, memberDefinitionRhs)
                  if defDefClass.isInstance(tree) then
                    defRhs.set(tree, memberDefinitionRhs)

              case _ =>

    catch
      case NonFatal(e) =>

    Ref(multitierPreprocessor).asExprOf[Any]
  end memberAscriptionImpl

  def memberDefinitionImpl[T](using Quotes)(body: Expr[T]): Expr[T] =
    import quotes.reflect.*

    try
      val commons = Commons()
      val reflectionExtensions = ReflectionExtensions()

      import commons.*
      import reflectionExtensions.*

      val context = ctx.invoke(quotes)
      val owner = scopeOwner(Symbol.spliceOwner)

      if owner.exists then
        val info = symbolInfo(owner)

        val underlyingResultType = info.resultType match
          case AppliedType(tycon, List(arg)) if tycon.typeSymbol.maybeOwner == multitierPreprocessor.moduleClass => arg
          case tpe => tpe

        val resultType =
          underlyingResultType match
            case AppliedType(tycon, List(valueType, peerType)) if placementType(tycon) && isNothing(valueType) =>
              tycon.appliedTo(List(`embedding.of`.typeRef.appliedTo(List(valueType, peerType)), peerType))
            case tpe if nonplacedMembers.remove(owner).isDefined =>
              `type`.typeRef.appliedTo(List(nonplaced.typeRef, tpe))
            case tpe =>
              tpe

        SymbolMutator.getOrErrorAndAbort.setInfo(owner, info.withResultType(resultType))

    catch
      case NonFatal(e) =>

    body
  end memberDefinitionImpl

  private def adaptMemberDefinitionBody(using Quotes)(tree: Any, hasPlacementType: Boolean) =
    val commons = Commons()
    val reflectionExtensions = ReflectionExtensions()

    import commons.*
    import reflectionExtensions.*
    import quotes.reflect.*

    val context = ctx.invoke(quotes)
    val tpt = valOrDefTpt.invoke(tree)
    val rhs = unforcedRhs.invoke(tree)

    SpannedPosition(Position.ofMacroExpansion.sourceFile, span.invoke(tree)):
      def maybePlacementRelatedTerm(tree: Any) = tree match
        case QuotesTree(
            Ident("on") |
            Select(Ident("language"), "on") |
            Select(Select(Ident("loci"), "language"), "on") |
            Select(Select(Select(Ident("_root_"), "loci"), "language"), "on")) =>
          true
        case _ =>
          false

      // propagate types for placement compounds and rewrite infix `and` to standard method invocation (if configured)
      val adaptedRhs =
        if propagateTypesForPlacementCompounds && hasPlacementType then
          val markerDef =
            withFlags.invoke(
              UntypedValDef(termName("<placement compound types propagated>"), TypedSplice(TypeTree.of[Boolean]), TypedSplice(Literal(BooleanConstant(true)))),
              Flags.Synthetic)

          def blockWithMarkerDef(tree: Any) =
            UntypedBlock(List(markerDef), tree)

          val placementType = tpt match
            case _ if infixOpClass.isInstance(tpt) => Some(left.invoke(tpt) -> right.invoke(tpt))
            case QuotesTree(Applied(_, args @ List(left, right))) => Some(left -> right)
            case _ => None

          placementType.fold(rhs): (value, peer) =>
            def adapt(left: Any, right: Any)(using SpannedPosition): Option[(AnyRef, Option[Any])] =
              propagate(left) flatMap: (left, leftPeer) =>
                propagate(right) map: (right, rightPeer) =>
                  val leftTypeApply = UntypedTypeApply(TypedSplice(Ref(and)), List(TypedSplice(TypeIdent(`embedding.on`)), value, leftPeer getOrElse peer))
                  val leftApply = UntypedApply(leftTypeApply, List(left))
                  val rightTypeApply = UntypedTypeApply(leftApply, List(value, value, rightPeer getOrElse peer, peer))
                  val rightApply = UntypedApply(rightTypeApply, List(right))
                  (rightApply, None)

            def underlying(tree: Any): Any =
              if parensClass.isInstance(tree) then underlying(forwardTo.invoke(tree)) else tree

            def propagate(tree: Any): Option[(AnyRef, Option[Any])] = underlying(tree) match
              case tree if infixOpClass.isInstance(tree) => (left.invoke(tree), op.invoke(tree), right.invoke(tree)) match
                case (left, QuotesTree(op @ Ident("and")), right) =>
                  SpannedPosition(Position.ofMacroExpansion.sourceFile, span.invoke(op)) { adapt(left, right) }
                case (QuotesTree(left @ TypeApply(fun, List(arg))), QuotesTree(op @ Ident("apply" | "local" | "sbj")), right) if maybePlacementRelatedTerm(fun) =>
                  Some(UntypedInfix(left, op, blockWithMarkerDef(right)), Some(arg))
                case _ =>
                  None
              case QuotesTree(Apply(tree @ Select(left, "and"), List(right))) =>
                SpannedPosition(Position.ofMacroExpansion.sourceFile, nameSpan.invoke(tree, context)) { adapt(left, right) }
              case QuotesTree(Apply(term @ TypeApply(fun, List(arg)), List(expr))) if maybePlacementRelatedTerm(fun) =>
                Some(UntypedApply(term, List(blockWithMarkerDef(expr))), Some(arg))
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
          val contextTree =
            val contextName = termName("<synthetic context>")
            val contextDef =
              withFlags.invoke(
                UntypedValDef(contextName, TypedSplice(TypeIdent(`Placed.Context`)), TypedSplice(Ref(erased).appliedToType(TypeRepr.of[Nothing]))),
                Flags.Synthetic)
            UntypedBlock(List(contextDef), UntypedIdent(contextName))

          val placedContext =
            setApplyKind.invoke(
              UntypedApply(TypedSplice(Ref(placed)), List(contextTree)),
              applyKindUsing)

          val paramDef =
            withFlags.invoke(
              UntypedValDef(termName("<synthetic context>"), UntypedTypeTree(), emptyTree),
              Flags.Synthetic | Flags.Param | Flags.Given)

          val contextFunction = UntypedFunction(List(paramDef), adaptedRhs)

          // the span of the right-hand-side macro application is extended to the entire definition
          // we use this extended span to identify the outer-most macro application when inferring context closures
          UntypedApply(placedContext, List(contextFunction))
        else
          adaptedRhs
      end placedRhs

      if placedRhs ne rhs then
        if valDefClass.isInstance(tree) then
          valRhs.set(tree, placedRhs)
        if defDefClass.isInstance(tree) then
          defRhs.set(tree, placedRhs)
  end adaptMemberDefinitionBody

  private def symbolInfo(using Quotes)(symbol: quotes.reflect.Symbol) =
    val info = classOf[quotes.reflect.SymbolMethods].getMethod("info", classOf[Object])
    info.invoke(quotes.reflect.SymbolMethods, symbol) match
      case tpe: quotes.reflect.TypeRepr @unchecked => tpe

  private def correctlyTyped(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    import quotes.reflect.*
    tpe match
      case _: TermRef | _: TypeRef | _: ConstantType | _: SuperType | _: Refinement |
           _: AppliedType | _: AnnotatedType | _: AndType | _: OrType | _: MatchType |
           _: ByNameType | _: ParamRef | _: ThisType | _: RecursiveThis | _: RecursiveType |
           _: MethodType | _: PolyType | _: TypeLambda | _: MatchCase | _: TypeBounds | _: NoPrefix =>
        true
      case _ =>
        false

  private final class Commons[Q <: Quotes & Singleton](using val quotes: Q):
    import quotes.reflect.*

    val multitierPreprocessor = '{ MultitierPreprocessor }.asTerm.underlyingArgument.symbol
    val `multitierPreprocessor.multitier` = TypeRepr.of[MultitierPreprocessor.multitier].typeSymbol

    val embedding = Symbol.requiredPackage("loci.embedding")
    val `language.on` = Symbol.requiredPackage("loci.language").typeMember("on")
    val `embedding.on` = Symbol.requiredPackage("loci.embedding").typeMember("on")
    val `embedding.of` = Symbol.requiredPackage("loci.embedding").typeMember("of")
    val `language.multitier` = Symbol.requiredClass("loci.language.multitier")
    val `embedding.multitier` = Symbol.requiredClass("loci.embedding.multitier")
    val `Placed.Context` = Symbol.requiredClass("loci.embedding.On.Placed.Context")
    val `type` = Symbol.requiredModule("loci.embedding.Multitier").typeMember("type")
    val nonplaced = Symbol.requiredClass("loci.embedding.Multitier.nonplaced")
    val peer = Symbol.requiredClass("loci.language.peer")
    val deferred = Symbol.requiredClass("loci.language.deferred")
    val placed = Symbol.requiredMethod("loci.language.placed")
//    val placed = Symbol.requiredMethod("loci.language.placed.apply")
    val and = Symbol.requiredMethod("loci.language.and")
    val erased = (Symbol.requiredPackage("loci.embedding").methodMember("erased") find { _.paramSymss.sizeIs == 1 }).get
    val compileTimeOnly = Symbol.requiredClass("scala.annotation.compileTimeOnly")
    val uninitialized = Symbol.requiredMethod("scala.compiletime.uninitialized")

    val placedValueCompileTimeOnlyAnnotation =
      New(TypeIdent(compileTimeOnly)).select(compileTimeOnly.primaryConstructor).appliedTo(Literal(StringConstant(illegalPlacedValueAccessMessage)))

    val objectMemberCompileTimeOnlyAnnotation =
      New(TypeIdent(compileTimeOnly)).select(compileTimeOnly.primaryConstructor).appliedTo(Literal(StringConstant(illegalObjectMemberAccessMessage)))

    val deferredAnnotation =
      New(TypeIdent(deferred)).select(deferred.primaryConstructor).appliedToNone

    def placementType(tpe: TypeRepr) =
      correctlyTyped(tpe) && !(tpe =:= TypeRepr.of[Nothing]) &&
      (tpe.typeSymbol == `language.on` || tpe.typeSymbol == `embedding.on`)

    def nonPlacementType(tpe: TypeRepr) =
      correctlyTyped(tpe) && !(tpe =:= TypeRepr.of[Nothing]) &&
      tpe.typeSymbol == `type`

    def isNothing(tpe: TypeRepr): Boolean = tpe match
      case _ if !correctlyTyped(tpe) || !(tpe <:< TypeRepr.of[Nothing]) => false
      case AnnotatedType(underlying, _) => isNothing(underlying)
      case AndType(left, right) => isNothing(left) || isNothing(right)
      case OrType(left, right) => isNothing(left) && isNothing(right)
      case Refinement(parent, name, _) => name != "on" && isNothing(parent)
      case _ => tpe.typeSymbol != `embedding.of`
  end Commons

  private object ReflectionExtensions:
    private var reflectionExtensions: Try[ReflectionExtensions] | Null = null

    inline def apply() =
      if reflectionExtensions == null then
        reflectionExtensions = Try { new ReflectionExtensions }
      reflectionExtensions.get
    end apply
  end ReflectionExtensions

  private final class ReflectionExtensions:
    private val setNext = classOf[::[?]].getMethod("next_$eq", classOf[List[?]])

    def setNext(init: ::[?], tail: List[?]): Unit =
      setNext.invoke(init, tail)
      scala.runtime.Statics.releaseFence()

    val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
    val contextsClass = Class.forName("dotty.tools.dotc.core.Contexts")
    val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
    val scopeClass = Class.forName("dotty.tools.dotc.core.Scopes$Scope")
    val compilationUnitClass = Class.forName("dotty.tools.dotc.CompilationUnit")
    val runClass = Class.forName("dotty.tools.dotc.Run")
    val symbolClass = Class.forName("dotty.tools.dotc.core.Symbols$Symbol")
    val symDenotationClass = Class.forName("dotty.tools.dotc.core.SymDenotations$SymDenotation")
    val annotationClass = Class.forName("dotty.tools.dotc.core.Annotations$Annotation")
    val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")
    val wildcardTypeClass = Class.forName("dotty.tools.dotc.core.Types$WildcardType$")
    val typerClass = Class.forName("dotty.tools.dotc.typer.Typer")
    val completerClass = Class.forName("dotty.tools.dotc.typer.Namer$Completer")
    val sourceFileClass = Class.forName("dotty.tools.dotc.util.SourceFile")
    val sourcePositionClass = Class.forName("dotty.tools.dotc.util.SourcePosition")
    val srcPosClass = Class.forName("dotty.tools.dotc.util.SrcPos")
    val positionedClass = Class.forName("dotty.tools.dotc.ast.Positioned")
    val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
    val namesClass = Class.forName("dotty.tools.dotc.core.Names")
    val nameClass = Class.forName("dotty.tools.dotc.core.Names$Name")
    val termNameClass = Class.forName("dotty.tools.dotc.core.Names$TermName")
    val applyKindClass = Class.forName("dotty.tools.dotc.ast.Trees$ApplyKind")
    val applyClass = Class.forName("dotty.tools.dotc.ast.Trees$Apply")
    val typeApplyClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeApply")
    val selectClass = Class.forName("dotty.tools.dotc.ast.Trees$Select")
    val identClass = Class.forName("dotty.tools.dotc.ast.Trees$Ident")
    val blockClass = Class.forName("dotty.tools.dotc.ast.Trees$Block")
    val newClass = Class.forName("dotty.tools.dotc.ast.Trees$New")
    val typeTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeTree")
    val defTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$DefTree")
    val namedDefTreeClass = Class.forName("dotty.tools.dotc.ast.Trees$NamedDefTree")
    val packageDefClass = Class.forName("dotty.tools.dotc.ast.Trees$PackageDef")
    val valOrDefDefClass = Class.forName("dotty.tools.dotc.ast.Trees$ValOrDefDef")
    val valDefClass = Class.forName("dotty.tools.dotc.ast.Trees$ValDef")
    val defDefClass = Class.forName("dotty.tools.dotc.ast.Trees$DefDef")
    val typeDefClass = Class.forName("dotty.tools.dotc.ast.Trees$TypeDef")
    val templateClass = Class.forName("dotty.tools.dotc.ast.Trees$Template")
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
    val run = contextClass.getMethod("run")
    val scope = contextClass.getMethod("scope")
    val owner = contextClass.getMethod("owner")
    val compilationUnit = contextClass.getMethod("compilationUnit")
    val outer = contextClass.getMethod("outer")
    val iterator = scopeClass.getMethod("iterator", contextClass)
    val untpdTree = compilationUnitClass.getMethod("untpdTree")
    val units = runClass.getMethod("units")
    val denot = symbolClass.getMethod("denot", contextClass)
    val infoOrCompleter = symDenotationClass.getMethod("infoOrCompleter")
    val unforcedDecls = symDenotationClass.getMethod("unforcedDecls", contextClass)
    val annotationsUnsafe = symDenotationClass.getMethod("annotationsUNSAFE", contextClass)
    val flagsUnsafe = symDenotationClass.getMethod("flagsUNSAFE")
    val resetFlag = symDenotationClass.getMethod("resetFlag", classOf[Long])
    val lazyAnnotation = annotationClass.getMethod("deferred", symbolClass, classOf[? => ?])
    val isEvaluated = annotationClass.getMethod("isEvaluated")
    val isEvaluating = annotationClass.getMethod("isEvaluating")
    val annotationSymbol = annotationClass.getMethod("symbol", contextClass)
    val annotationTree = annotationClass.getMethod("tree", contextClass)
    val wildcardType = wildcardTypeClass.getDeclaredField("MODULE$")
    val typedExpr = typerClass.getMethod("typedExpr", treeClass, typeClass, contextClass)
    val typedType = typerClass.getMethod("typedType", treeClass, typeClass, classOf[Boolean], contextClass)
    val typedAheadExpr = typerClass.getMethod("typedAheadExpr", treeClass, typeClass, contextClass)
    val original = completerClass.getMethod("original")
    val contains = sourcePositionClass.getMethod("contains", sourcePositionClass)
    val sourcePos = srcPosClass.getMethod("sourcePos", contextClass)
    val span = srcPosClass.getMethod("span")
    val withSpan = positionedClass.getMethod("withSpan", classOf[Long])
    val isEmpty = treeClass.getMethod("isEmpty")
    val hasType = treeClass.getMethod("hasType")
    val termName = namesClass.getMethod("termName", classOf[String])
    val typeName = namesClass.getMethod("typeName", classOf[String])
    val apply = applyClass.getMethod("apply", treeClass, classOf[List[?]], sourceFileClass)
    val fun = applyClass.getMethod("fun")
    val setApplyKind = applyClass.getMethod("setApplyKind", applyKindClass)
    val typeApply = typeApplyClass.getMethod("apply", treeClass, classOf[List[?]], sourceFileClass)
    val select = selectClass.getMethod("apply", treeClass, nameClass, sourceFileClass)
    val qualifier = selectClass.getMethod("qualifier")
    val nameSpan = selectClass.getMethod("nameSpan", contextClass)
    val ident = identClass.getMethod("apply", nameClass, sourceFileClass)
    val block = blockClass.getMethod("apply", classOf[List[?]], treeClass, sourceFileClass)
    val newctor = newClass.getMethod("apply", treeClass, sourceFileClass)
    val typeTree = typeTreeClass.getMethod("apply", sourceFileClass)
    val rawMods = defTreeClass.getMethod("rawMods")
    val setMods = defTreeClass.getMethod("setMods", modifiersClass)
    val namePos = namedDefTreeClass.getMethod("namePos", contextClass)
    val packageStats = packageDefClass.getMethod("stats")
    val valOrDefTpt = valOrDefDefClass.getMethod("tpt")
    val unforcedRhs = valOrDefDefClass.getMethod("unforcedRhs")
    val withFlags = valOrDefDefClass.getMethod("withFlags", classOf[Long])
    val valDef = valDefClass.getMethod("apply", termNameClass, treeClass, classOf[Object], sourceFileClass)
    val valTpt = valDefClass.getDeclaredField("tpt")
    val valRhs = valDefClass.getDeclaredField("preRhs")
    val defTpt = defDefClass.getDeclaredField("tpt")
    val defRhs = defDefClass.getDeclaredField("preRhs")
    val paramss = defDefClass.getMethod("paramss")
    val rhs = typeDefClass.getMethod("rhs")
    val unforcedBody = templateClass.getMethod("unforcedBody")
    val lo = typeBoundsTreeClass.getMethod("lo")
    val hi = typeBoundsTreeClass.getMethod("hi")
    val alias = typeBoundsTreeClass.getMethod("alias")
    val refinedTpt = refinedTypeTreeClass.getDeclaredField("tpt")
    val tpt = refinedTypeTreeClass.getMethod("tpt")
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
    val modWithAddedAnnotation = modifiersClass.getMethod("withAddedAnnotation", treeClass)

    val noContext = contextsClass.getMethod("NoContext").invoke(null)
    val applyKindUsing = applyKindClass.getMethod("valueOf", classOf[String]).invoke(null, "Using")
    val emptyTree = untpdClass.getMethod("EmptyTree").invoke(null)

    valTpt.setAccessible(true)
    valRhs.setAccessible(true)
    defTpt.setAccessible(true)
    defRhs.setAccessible(true)
    refinedTpt.setAccessible(true)
    appliedTypeTreeArgs.setAccessible(true)
    infixLeft.setAccessible(true)

    case class SpannedPosition(sourceFile: Any, span: Any)

    object SpannedPosition:
      def apply[T](sourceFile: Any, span: Any)(body: SpannedPosition ?=> T): T =
        body(using SpannedPosition(sourceFile, span))
      def apply[T](using Quotes)(pos: quotes.reflect.Position)(body: SpannedPosition ?=> T): T =
        body(using SpannedPosition(pos.sourceFile, span.invoke(pos)))

    inline def UntypedApply(fun: Any, args: Any)(using pos: SpannedPosition) =
      withSpan.invoke(apply.invoke(null, fun, args, pos.sourceFile), pos.span)

    inline def UntypedTypeApply(fun: Any, args: Any)(using pos: SpannedPosition) =
      withSpan.invoke(typeApply.invoke(null, fun, args, pos.sourceFile), pos.span)

    inline def UntypedApplied(tpt: Any, args: Any)(using pos: SpannedPosition) =
      withSpan.invoke(appliedTypeTree.invoke(null, tpt, args, pos.sourceFile), pos.span)

    inline def UntypedSelect(qualifier: Any, name: Any)(using pos: SpannedPosition) =
      withSpan.invoke(select.invoke(null, qualifier, name, pos.sourceFile), pos.span)

    inline def UntypedIdent(name: Any)(using pos: SpannedPosition) =
      withSpan.invoke(ident.invoke(null, name, pos.sourceFile), pos.span)

    inline def UntypedInfix(left: Any, op: Any, right: Any)(using pos: SpannedPosition) =
      withSpan.invoke(infix.invoke(null, left, op, right, pos.sourceFile), pos.span)

    inline def UntypedNew(tpt: Any)(using pos: SpannedPosition) =
      withSpan.invoke(newctor.invoke(null, tpt, pos.sourceFile), pos.span)

    inline def UntypedBlock(stats: Any, expr: Any)(using pos: SpannedPosition) =
      withSpan.invoke(block.invoke(null, stats, expr, pos.sourceFile), pos.span)

    inline def UntypedFunction(args: Any, body: Any)(using pos: SpannedPosition) =
      withSpan.invoke(function.invoke(null, args, body, pos.sourceFile), pos.span)

    inline def UntypedTypeTree()(using pos: SpannedPosition) =
      withSpan.invoke(typeTree.invoke(null, pos.sourceFile), pos.span)

    inline def UntypedValDef(name: Any, tpt: Any, rhs: Any)(using pos: SpannedPosition) =
      withSpan.invoke(valDef.invoke(null, name, tpt, rhs, pos.sourceFile), pos.span)

    inline def TypedSplice(using Quotes)(tree: quotes.reflect.Tree) =
      typedSplice.invoke(null, tree, false, ctx.invoke(quotes))

    inline def typeName(name: String): Any =
      typeName.invoke(null, name)

    inline def termName(name: String): Any =
      termName.invoke(null, name)

    object QuotesSymbol:
      def unapply(using Quotes)(symbol: Any): Option[quotes.reflect.Symbol] = symbol match
        case symbol: quotes.reflect.Symbol @unchecked if symbolClass.isInstance(symbol) => Some(symbol)
        case _ => None

    object QuotesTree:
      def unapply(using Quotes)(tree: Any): Option[quotes.reflect.Tree] = tree match
        case tree: quotes.reflect.Tree @unchecked if treeClass.isInstance(tree) => Some(tree)
        case _ => None

    def scopeOwner(using Quotes)(symbol: quotes.reflect.Symbol): quotes.reflect.Symbol =
      if symbol.exists &&
         (symbol.isLocalDummy ||
          symbol.isAnonymousFunction ||
          (flags(symbol) is quotes.reflect.Flags.Macro) ||
          !symbol.isValDef && !symbol.isDefDef && !symbol.isClassDef) then
        scopeOwner(symbol.maybeOwner)
      else
        symbol

    private def constructScopeIterator(using Quotes)(
        context: Any,
        scopeOwner: Option[(quotes.reflect.Symbol, Boolean)],
        foundScopeOwner: Boolean): Iterator[quotes.reflect.Symbol] =
      val (found, include, terminate) = scopeOwner.fold(false, true, false): (symbol, nested) =>
        val found = owner.invoke(context) == symbol
        (found, found || nested, foundScopeOwner && !found)

      if !terminate && context != noContext then
        val symbols =
          if include then
            iterator.invoke(scope.invoke(context), context) match
              case symbols: Iterator[?] =>
                symbols flatMap:
                  case QuotesSymbol(symbol) => Some(symbol)
                  case _ => None
              case _ =>
                Iterator.empty
          else
            Iterator.empty

        constructScopeIterator(outer.invoke(context), scopeOwner, found) ++ symbols
      else
        Iterator.empty
    end constructScopeIterator

    def scopeIterator(using Quotes) =
      constructScopeIterator(ctx.invoke(quotes), None, false)

    def scopeIterator(using Quotes)(symbol: quotes.reflect.Symbol) =
      constructScopeIterator(ctx.invoke(quotes), Some(symbol, false), false)

    def nestedScopeIterator(using Quotes)(symbol: quotes.reflect.Symbol) =
      constructScopeIterator(ctx.invoke(quotes), Some(symbol, true), false)

    def tryTypingTerm(using Quotes)(term: quotes.reflect.Term) =
      if hasType.invoke(term) == false then
        noReporting(ctx.invoke(quotes))(None, useExploringContext = false): context =>
          typedExpr.invoke(typer.invoke(context), term, wildcardType.get(null), context) match
            case QuotesTree(term: quotes.reflect.Term) => Some(term)
            case _ => None
      else
        Some(term)

    def tryTypingTypeTree(using Quotes)(tpt: quotes.reflect.TypeTree) =
      if hasType.invoke(tpt) == false then
        noReporting(ctx.invoke(quotes))(None, useExploringContext = false): context =>
          typedType.invoke(typer.invoke(context), tpt, wildcardType.get(null), false, context) match
            case QuotesTree(tpt: quotes.reflect.TypeTree) => Some(tpt)
            case _ => None
      else
        Some(tpt)

    def completerOriginalTree(using Quotes)(symbol: quotes.reflect.Symbol) =
      val info = infoOrCompleter.invoke(denot.invoke(symbol, ctx.invoke(quotes)))
      Option.when(completerClass.isInstance(info)) { original.invoke(info) }

    def declarationsOfSymbol(using Quotes)(symbol: quotes.reflect.Symbol) =
      completerOriginalTree(symbol) match
        case Some(tree) =>
          declarationsOfTree(tree)
        case _ =>
          try
            if symbol.isClassDef || symbol.isPackageDef || (flags(symbol) is quotes.reflect.Flags.Module) then
              val context = ctx.invoke(quotes)
              iterator.invoke(unforcedDecls.invoke(denot.invoke(symbol, context), context), context) match
                case symbols: Iterator[?] =>
                  val iterator = symbols flatMap:
                    case QuotesSymbol(symbol) => Some(symbol)
                    case _ => None
                  iterator.toList
                case _ =>
                  List.empty
            else
              List.empty
          catch case NonFatal(_) =>
            List.empty

    def declarationsOfTree(tree: Any) =
      val statements =
        if packageDefClass.isInstance(tree) then
          Some(packageStats.invoke(tree))
        else
          val template =
            if typeDefClass.isInstance(tree) then Some(rhs.invoke(tree))
            else if moduleDefClass.isInstance(tree) then Some(impl.invoke(tree))
            else None
          template map: template =>
            if templateClass.isInstance(template) then unforcedBody.invoke(template)
            else List.empty
      statements match
        case Some(stats: List[?]) =>
          stats filter: stat =>
            valDefClass.isInstance(stat) ||
            defDefClass.isInstance(stat) ||
            typeDefClass.isInstance(stat) ||
            moduleDefClass.isInstance(stat) ||
            packageDefClass.isInstance(stat)
        case _ =>
          List.empty

    def declarations(using Quotes)(decl: Any) = decl match
      case QuotesSymbol(symbol) => declarationsOfSymbol(symbol)
      case _ => declarationsOfTree(decl)

    def annotationIteratorOfSymbol(using Quotes)(symbol: quotes.reflect.Symbol) =
      val context = ctx.invoke(quotes)
      val isModuleDef = flags(symbol) is quotes.reflect.Flags.Module
      val isClassDef = symbol.isClassDef
      val symbols =
        Iterator(symbol) ++
        (if isModuleDef && isClassDef then Iterator(symbol.companionModule) else Iterator.empty) ++
        (if isModuleDef && !isClassDef then Iterator(symbol.moduleClass) else Iterator.empty)
      val symbolAnnotations = symbols flatMap: symbol =>
        annotationsUnsafe.invoke(denot.invoke(symbol, context), context) match
          case annotations: List[?] =>
            annotations flatMap: annotation =>
              Option.when(isEvaluated.invoke(annotation) == true):
                annotationTree.invoke(annotation, context)
          case _ =>
            List.empty
      (completerOriginalTree(symbol).iterator flatMap annotationIteratorOfTree) ++ symbolAnnotations

    def annotationIteratorOfTree(tree: Any) =
      if defTreeClass.isInstance(tree) then
        modAnnotations.invoke(rawMods.invoke(tree)) match
          case trees: List[?] => trees.iterator
          case _ => Iterator.empty
      else
        Iterator.empty

    def annotationIterator(using Quotes)(decl: Any) = decl match
      case QuotesSymbol(symbol) => annotationIteratorOfSymbol(symbol)
      case tree => annotationIteratorOfTree(tree)

    def annotationIndex(using Quotes)(decl: Any)(predicate: Any => Boolean) =
      import quotes.reflect.*

      def annotationIndexByTree(tree: Any) =
        if defTreeClass.isInstance(tree) then
          modAnnotations.invoke(rawMods.invoke(tree)) match
            case trees: List[?] => trees indexWhere predicate
            case _ => -1
        else
          -1

      def annotationIndexBySymbol(symbol: Symbol) =
        val context = ctx.invoke(quotes)
        val index = annotationsUnsafe.invoke(denot.invoke(symbol, context), context) match
          case annotations: List[?] => annotations indexWhere { annotation => predicate(annotationSymbol.invoke(annotation, context)) }
          case _ => -1
        if index == -1 then
          completerOriginalTree(symbol).fold(-1) { annotationIndexByTree }
        else
          index

      decl match
        case QuotesSymbol(symbol) => annotationIndexBySymbol(symbol)
        case tree => annotationIndexByTree(tree)
    end annotationIndex

    def hasAnnotation(using Quotes)(decl: Any)(predicate: Any => Boolean) =
      annotationIndex(decl)(predicate) >= 0

    def isAnnotationTreeSymbol(using Quotes)(tree: quotes.reflect.Tree, annotationSymbol: quotes.reflect.Symbol) =
      import quotes.reflect.*

      def checkTypedTree(tree: Tree): Boolean = tree match
        case Apply(fun, _) => checkTypedTree(fun)
        case TypeApply(fun, _) => checkTypedTree(fun)
        case Select(qualifier, _) => checkTypedTree(qualifier)
        case New(tpt) => tpt.symbol == annotationSymbol
        case _ => false

      def checkUntypedTree(tree: Tree): Boolean = tree match
        case _ if typedSpliceClass.isInstance(tree) => splice.invoke(tree) match
          case QuotesTree(tree) => checkTypedTree(tree)
          case _ => false
        case _ if hasType.invoke(tree) == true =>
          checkTypedTree(tree)
        case Apply(fun, _) =>
          checkUntypedTree(fun)
        case TypeApply(fun, _) =>
          checkUntypedTree(fun)
        case Select(qualifier, _) =>
          checkUntypedTree(qualifier)
        case New(tpt) if typedSpliceClass.isInstance(tpt) => splice.invoke(tpt) match
          case QuotesTree(tree) => tree.symbol == annotationSymbol
          case _ => false
        case New(tpt) =>
          tryTypingTypeTree(tpt) exists: tpt =>
            correctlyTyped(tpt.tpe) && tpt.symbol == annotationSymbol
        case _ =>
          false

      checkUntypedTree(tree)
    end isAnnotationTreeSymbol

    def annotationSymbolIndex(using Quotes)(decl: Any, annotationSymbol: quotes.reflect.Symbol) =
      annotationIndex(decl):
        case QuotesSymbol(symbol) => symbol == annotationSymbol
        case QuotesTree(tree) => isAnnotationTreeSymbol(tree, annotationSymbol)
        case _ => false

    def hasAnnotationSymbol(using Quotes)(decl: Any, annotationSymbol: quotes.reflect.Symbol) =
      annotationSymbolIndex(decl, annotationSymbol) >= 0

    def flags(using Quotes)(decl: Any) =
      val flags = decl match
        case QuotesSymbol(symbol) => flagsUnsafe.invoke(denot.invoke(symbol, ctx.invoke(quotes)))
        case tree => modFlags.invoke(rawMods.invoke(tree))
      flags match
        case flags: quotes.reflect.Flags @unchecked if classOf[java.lang.Long].isInstance(flags) => flags
        case _ => quotes.reflect.Flags.EmptyFlags

    def position(using Quotes)(decl: Any) =
      sourcePos.invoke(decl, ctx.invoke(quotes)) match
        case pos: quotes.reflect.Position @unchecked if sourcePositionClass.isInstance(pos) => Some(pos)
        case _ => None

    def macroAnnotteeNamePosition(using Quotes) =
      import quotes.reflect.*
      val context = ctx.invoke(quotes)

      def macroAnnotteeNamePosition(tree: Any): Option[quotes.reflect.Position] =
        if namedDefTreeClass.isInstance(tree) &&
           (position(tree) exists { pos => pos.sourceFile == SourceFile.current || pos.sourceFile == Position.ofMacroExpansion.sourceFile }) &&
           (annotationIterator(tree) exists { tree => contains.invoke(sourcePos.invoke(tree, context), Position.ofMacroExpansion) == true }) then
          namePos.invoke(tree, context)  match
            case pos: Position @unchecked if sourcePositionClass.isInstance(pos) => Some(pos)
            case _ => None
        else
          tree match
            case iterable: Iterable[?] => iterable collectFirst Function.unlift(macroAnnotteeNamePosition)
            case product: Product => product.productIterator collectFirst Function.unlift(macroAnnotteeNamePosition)
            case _ => None

      macroAnnotteeNamePosition(untpdTree.invoke(compilationUnit.invoke(ctx.invoke(quotes))))
    end macroAnnotteeNamePosition

    def macroAnnotteeDeclarations(using Quotes) =
      import quotes.reflect.*

      val context = ctx.invoke(quotes)
      val owner = scopeOwner(Symbol.spliceOwner)
      val annotteePos = macroAnnotteeNamePosition

      val decls = declarations(owner).iterator ++ nestedScopeIterator(owner) filter: decl =>
        inline def declPos =
          if namedDefTreeClass.isInstance(decl) then
            Some(namePos.invoke(decl, context))
          else
            position(decl) flatMap: pos =>
              Option.when((pos.sourceFile == SourceFile.current || pos.sourceFile == Position.ofMacroExpansion.sourceFile) && pos.toString != "?"):
                Position(pos.sourceFile, pos.start, pos.start)

        val evaluating =
          decl match
            case QuotesSymbol(symbol) => annotationsUnsafe.invoke(denot.invoke(symbol, context), context) match
              case annotations: List[?] => annotations exists { isEvaluating.invoke(_) == true }
              case _ => false
            case _ => false

        (position(decl) exists { pos => pos.sourceFile == SourceFile.current || pos.sourceFile == Position.ofMacroExpansion.sourceFile }) &&
        (evaluating ||
         (annotationIterator(decl) exists { tree => contains.invoke(sourcePos.invoke(tree, context), Position.ofMacroExpansion) == true }) ||
         (annotteePos exists { pos => declPos exists { contains.invoke(pos, _) == true } }))
      end decls

      decls.distinct.toList
    end macroAnnotteeDeclarations
  end ReflectionExtensions
end MultitierPreprocessor
