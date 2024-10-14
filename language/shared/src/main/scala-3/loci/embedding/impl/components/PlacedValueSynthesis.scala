package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.mutable

object PlacedValueSynthesis:
  private val synthesizedDefinitionsCache = mutable.Map.empty[Any, Any]
  private val synthesizedStatementsCache = mutable.Map.empty[Any, Any]
  private val synthesizedPlacedValuesCache = mutable.Map.empty[Any, Any]

@experimental
trait PlacedValueSynthesis:
  this: Component & Commons & Annotations & SymbolTrees & PlacedTransformations & Placements & NonPlacements & Peers =>
  import quotes.reflect.*

  case class SynthesizedPlacedValues(symbol: Symbol, module: Symbol, peer: Symbol, parents: List[TypeRepr])
  case class SynthesizedDefinitions(original: Symbol, binding: Symbol, init: Option[Symbol], setter: Option[Symbol], impls: List[Symbol])
  case class SynthesizedStatements(binding: Symbol, impls: List[Symbol])

  private val synthesizedDefinitionsCache = PlacedValueSynthesis.synthesizedDefinitionsCache match
    case cache: mutable.Map[Symbol, (SynthesizedDefinitions, Boolean)] @unchecked => cache
  private val synthesizedStatementsCache = PlacedValueSynthesis.synthesizedStatementsCache match
    case cache: mutable.Map[(Symbol, Symbol, Int) | Symbol, Option[SynthesizedStatements]] @unchecked => cache
  private val synthesizedPlacedValuesCache = PlacedValueSynthesis.synthesizedPlacedValuesCache match
    case cache: mutable.Map[(Symbol, Symbol) | Symbol, (SynthesizedPlacedValues, Boolean)] @unchecked => cache

  private def mangledSymbolName(symbol: Symbol) =
    f"loci$$${s"${implementationForm(symbol)} ${fullName(symbol)}".hashCode}%08x"

  private def implementationForm(symbol: Symbol) =
    if symbol.flags is Flags.Module then "object"
    else if symbol.flags is Flags.Trait then "trait"
    else "class"

  private def syntheticTrait(
      owner: Symbol,
      name: String,
      mangledName: String,
      parents: List[TypeRepr],
      selfType: Option[TypeRepr],
      noInits: Boolean,
      enterSymbol: Boolean)(
      decls: Symbol => List[Symbol]) =
    owner.typeMember(name) orElse owner.typeMember(mangledName) orElse:
      val flags = Flags.Synthetic | Flags.Trait | (if noInits then Flags.NoInits else Flags.EmptyFlags)
      val symbol = newClass(owner, if canMakeTargetName then name else mangledName, flags, parents, decls, selfType)
      tryMakeTargetName(symbol, mangledName)
      if enterSymbol then
        SymbolMutator.getOrErrorAndAbort.enter(owner, symbol)
      symbol

  private def copyAnnotations(from: Symbol, to: Symbol, decrementContextResultCount: Boolean, sameTargetName: Boolean) =
    def updateSymbolAnnotationWithTree(symbol: Symbol, tree: Tree): Unit =
      SymbolMutator.get.fold(
        report.warning("Annotations in multitier modules are ignored with current compiler version.", from.annotations.head.posInUserCode)):
        _.updateAnnotationWithTree(symbol, tree)

    from.annotations foreach:
      case tree @ Apply(fun, List(arg @ Literal(IntConstant(count))))
          if fun.symbol.isClassConstructor && fun.symbol.owner == symbols.contextResultCount && decrementContextResultCount =>
        if count > 1 then
          updateSymbolAnnotationWithTree(to, Apply.copy(tree)(fun, List(Literal.copy(arg)(IntConstant(count - 1)))))

      case Apply(fun, List(arg @ Literal(StringConstant(message))))
        if fun.symbol.isClassConstructor && fun.symbol.owner == symbols.compileTimeOnly &&
           (message == MultitierPreprocessor.illegalPlacedValueAccessMessage ||
            message == MultitierPreprocessor.illegalObjectMemberAccessMessage) =>

      case Apply(fun, List(_))
        if fun.symbol.isClassConstructor && fun.symbol.owner == symbols.targetName && !sameTargetName =>

      case Apply(fun, List())
        if fun.symbol.isClassConstructor && fun.symbol.owner == symbols.deferred && (to.flags is Flags.Deferred) =>

      case tree =>
        updateSymbolAnnotationWithTree(to, tree)
  end copyAnnotations

  private def erasePlacementAndNonPlacementType(info: TypeRepr) =
    PlacementInfo(info.resultType) match
      case Some(placementInfo) =>
        val erasedInfo = placementInfo.modality match
          case Modality.Subjective(peerType) =>
            info.withResultType(symbols.function1.typeRef.appliedTo(List(symbols.remote.typeRef.appliedTo(peerType), placementInfo.valueType)))
          case _ =>
            info.withResultType(placementInfo.valueType)
        erasedInfo -> placementInfo.peerType.typeSymbol
      case _ =>
        NonPlacementInfo(info.resultType) match
          case Some(nonPlacementInfo) =>
            info.withResultType(nonPlacementInfo.valueType) -> defn.AnyClass
          case _ =>
            info -> defn.AnyClass

  private class MultitierModuleTypeUnlifter(base: Option[TypeRepr]) extends TypeMap(quotes):
    private var nestedInAugmentation = false
    private var underlyingSymbolToUnlift = Option.empty[Symbol]

    private inline def inNestedAugmentation[T](nested: Boolean)(body: => T) =
      val previousNestedInAugmentation = nestedInAugmentation
      nestedInAugmentation = nested
      val result = body
      nestedInAugmentation = previousNestedInAugmentation
      result

    private inline def unlift(tpe: TypeRepr, symbol: Symbol) =
      if nestedInAugmentation then
        underlyingSymbolToUnlift = Some(symbol)
        tpe
      else
        underlyingSymbolToUnlift = None
        base match
          case Some(base) if base <:< tpe => base.select(synthesizedPlacedValues(symbol, defn.AnyClass).symbol)
          case _ => tpe.select(synthesizedPlacedValues(symbol, defn.AnyClass).symbol)

    private inline def preserve(tpe: TypeRepr) =
      underlyingSymbolToUnlift = None
      tpe

    private def dealiasUpperBounds(tpe: TypeRepr): TypeRepr =
      tpe.dealias match
        case tpe: TypeBounds =>
          tpe.hi
        case tpe =>
          val symbol = tpe.typeSymbol
          if symbol.exists && !symbol.isClassDef && symbol.isAbstractType then
            symbol.info match
              case tpe: TypeBounds => dealiasUpperBounds(tpe.hi)
              case _ => tpe
          else
            tpe

    override def transform(tpe: TypeRepr) = tpe match
      case tpe: AnnotatedType =>
        val underlying = inNestedAugmentation(true) { transform(tpe.underlying) }
        val result = if underlying != tpe.underlying then AnnotatedType(underlying, tpe.annotation) else tpe
        underlyingSymbolToUnlift.fold(result) { unlift(result, _) }
      case tpe: Refinement =>
        val parent = inNestedAugmentation(true) { transform(tpe.parent) }
        val result = if parent != tpe.parent then Refinement(parent, tpe.name, tpe.info) else tpe
        underlyingSymbolToUnlift.fold(result) { unlift(result, _) }
      case tpe: AppliedType =>
        val tycon = transform(tpe.tycon)
        if tycon != tpe.tycon then AppliedType(tycon, tpe.args) else tpe
      case tpe: MethodType =>
        val methodType = MethodType(tpe.paramNames)(_ => tpe.paramTypes, _ => inNestedAugmentation(true) { transform(tpe.resType) })
        if methodType != tpe then methodType else tpe
      case tpe: PolyType =>
        val polyType = PolyType(tpe.paramNames)(_ => tpe.paramBounds, _ => inNestedAugmentation(true) { transform(tpe.resType) })
        if polyType != tpe then polyType else tpe
      case tpe: TypeLambda =>
        val typeLambda = TypeLambda(tpe.paramNames, _ => tpe.paramBounds, _ => inNestedAugmentation(true) { transform(tpe.resType) })
        if typeLambda != tpe then typeLambda else tpe
      case AndType(left, right) =>
        def lift(tpe: TypeRepr) =
          if tpe.baseClasses exists isMultitierModule then inNestedAugmentation(false) { transform(tpe) } else defn.AnyClass.typeRef
        val leftLifted = lift(left)
        val rigthLifted = lift(right)
        if leftLifted.typeSymbol == defn.AnyClass then rigthLifted
        else if rigthLifted.typeSymbol == defn.AnyClass then leftLifted
        else AndType(leftLifted, rigthLifted)
      case _ =>
        val dealiased = dealiasUpperBounds(tpe)
        val result = dealiased match
          case tpe: NamedType => tpe
          case _ => inNestedAugmentation(false) { super.transform(dealiased) }
        if result == dealiased then
          val symbol = result.typeSymbol
          if symbol.exists && isMultitierModule(symbol) then
            unlift(tpe, symbol)
          else
            preserve(tpe)
        else
          preserve(result)
  end MultitierModuleTypeUnlifter

  private def synthesizedValOrDef(symbol: Symbol): SynthesizedDefinitions =
    val preprocessedTree = symbolPreprocessedTree(symbol)

    val synthesizedDefinition =
      synthesizedDefinitionsCache.get(symbol) collect:
        case (synthesizedDefinition, hasPreprocessedTree) if preprocessedTree.isEmpty || hasPreprocessedTree => synthesizedDefinition

    synthesizedDefinition getOrElse:
      val multitierModule = isMultitierModule(symbol)
      val placedName = s"<${names.placedValue} ${symbol.name} of ${fullName(symbol.owner)}>"

      val potentialGetterName = if symbol.name endsWith "_=" then symbol.name.dropRight(2) else ""
      val potentialGetter = if potentialGetterName.nonEmpty then symbol.owner.declaredField(potentialGetterName) else Symbol.noSymbol

      val (universalName, info, peer, getter) =
        symbol.info match
          case MethodType(List(paramName), List(paramType), resultType) if resultType.typeSymbol == defn.UnitClass && potentialGetter.exists =>
            val name =
              if symbol.flags is Flags.Private then
                s"<${names.placedPrivateValue} $potentialGetterName of ${fullName(symbol.owner)}>_="
              else
                symbol.name
            val (info, _) = erasePlacementAndNonPlacementType(paramType)
            (name, MethodType(List(paramName))(_ => List(info), _ => resultType), defn.AnyClass, potentialGetter)
          case tpe =>
            if multitierModule then
              val multitierModuleTypeUnlifter = MultitierModuleTypeUnlifter(Some(symbol.termRef))
              (symbol.name, multitierModuleTypeUnlifter.transform(tpe), defn.AnyClass, Symbol.noSymbol)
            else
              val name = if symbol.flags is Flags.Private then s"<${names.placedPrivateValue} ${symbol.name} of ${fullName(symbol.owner)}>" else symbol.name
              val (info, peer) = erasePlacementAndNonPlacementType(symbol.info)
              (name, if hasSyntheticMultitierContextArgument(symbol) then dropLastArgumentList(info) else info, peer, Symbol.noSymbol)

      val peers =
        val rhs = preprocessedTree collect:
          case PlacedStatement(ValDef(_, _, Some(rhs))) => rhs
          case PlacedStatement(DefDef(_, _, _, Some(rhs))) => rhs
          case NonPlacedStatement(ValDef(_, _, Some(rhs))) => rhs
          case NonPlacedStatement(DefDef(_, _, _, Some(rhs))) => rhs

        val peers =
          rhs.toList flatMap: rhs =>
            extractPlacementBodies(rhs) flatMap: (_, tpe) =>
              tpe flatMap: tpe =>
                PlacementInfo(tpe) map: placementInfo =>
                  placementInfo.peerType.typeSymbol

        (if peers contains peer then peers else peer :: peers) filterNot { _ == defn.AnyClass }
      end peers

      val universalValues = synthesizedPlacedValues(symbol.owner, defn.AnyClass).symbol
      val placedValues = peers map { synthesizedPlacedValues(symbol.owner, _).symbol }

      val synthesizedDefinition =
        synthesizedDefinitionsCache.get(symbol) collect :
          case (synthesizedDefinition, hasPreprocessedTree) if preprocessedTree.isEmpty || hasPreprocessedTree => synthesizedDefinition

      synthesizedDefinition getOrElse :
        val decrementContextResultCount = info != symbol.info
        val universalOnly = peer == defn.AnyClass && peers.sizeIs == 1 || (symbol.flags is Flags.Deferred) || multitierModule
        val flags =
          if multitierModule then symbol.flags | Flags.Deferred
          else if universalOnly then symbol.flags
          else symbol.flags &~ Flags.PrivateLocal

        val universal = universalValues.declaredField(universalName) orElse:
          val universal = newVal(universalValues, universalName, info, flags, Symbol.noSymbol)
          copyAnnotations(symbol, universal, decrementContextResultCount, sameTargetName = true)
          universal

        val setter =
          if (symbol.flags is Flags.Mutable | Flags.PrivateLocal) &&
             symbol.isField &&
             !symbol.isFieldAccessor &&
             !symbol.setter.exists then
            val setterInfo = MethodType(List("x$1"))(_ => List(info), _ => TypeRepr.of[Unit])
            val setterFlags = if flags is Flags.Synthetic then Flags.Synthetic else Flags.EmptyFlags
            Some(newMethod(universalValues, s"${universalName}_=", setterInfo, setterFlags | Flags.FieldAccessor | Flags.Method | Flags.Mutable, Symbol.noSymbol))
          else
            None

        val definition =
          if !universalOnly then
            if symbol.isMethod then
              val impls = placedValues map: placedValues =>
                placedValues.declaredMethod(universalName) find { _.info =:= info } getOrElse:
                  val placed = newMethod(placedValues, universalName, info, flags | Flags.Synthetic | Flags.Override, Symbol.noSymbol)
                  copyAnnotations(symbol, placed, decrementContextResultCount, sameTargetName = true)
                  placed
              SynthesizedDefinitions(symbol, universal, None, setter, impls)
            else
              val methodType = MethodType(List.empty)(_ => List.empty, _ => info)

              val universalInit = universalValues.declaredField(placedName) orElse:
                newMethod(universalValues, placedName, methodType, Flags.Synthetic, Symbol.noSymbol)

              val implsInit = placedValues map: placedValues =>
                placedValues.declaredField(placedName) orElse:
                  val placedInit = newMethod(placedValues, placedName, methodType, Flags.Synthetic | Flags.Override, Symbol.noSymbol)
                  copyAnnotations(symbol, placedInit, decrementContextResultCount, sameTargetName = false)
                  placedInit

              SynthesizedDefinitions(symbol, universal, Some(universalInit), setter, implsInit)
          else
            SynthesizedDefinitions(symbol, universal, None, setter, List.empty)
        end definition

        synthesizedDefinitionsCache += symbol -> (definition -> preprocessedTree.isDefined)
        synthesizedDefinitionsCache += definition.binding -> (definition -> preprocessedTree.isDefined)
        definition.init foreach { synthesizedDefinitionsCache += _ -> (definition -> preprocessedTree.isDefined) }
        definition.impls foreach { synthesizedDefinitionsCache += _ -> (definition -> preprocessedTree.isDefined) }
        definition
  end synthesizedValOrDef

  private def synthesizedModule(symbol: Symbol): SynthesizedDefinitions =
    val (synthesizedDefinition, _) = synthesizedDefinitionsCache.getOrElse(symbol -> true, {
      val module = if symbol.moduleClass.exists then symbol.moduleClass else symbol
      val modulePlacedValues = synthesizedPlacedValues(module, defn.AnyClass).symbol
      val ownerPlacedValues = synthesizedPlacedValues(module.owner, defn.AnyClass).symbol
      synthesizedDefinitionsCache.getOrElse(module -> true, {
        val flags = ownerPlacedValues.fieldMember(module.companionModule.name).fold(Flags.EmptyFlags): symbol =>
          if symbol.flags is Flags.Lazy then Flags.Lazy else Flags.EmptyFlags
        val binding = ownerPlacedValues.declaredField(module.companionModule.name) orElse:
          newVal(ownerPlacedValues, module.companionModule.name, modulePlacedValues.typeRef, flags | Flags.Deferred, Symbol.noSymbol)
        val definition = SynthesizedDefinitions(module, binding, None, None, List.empty)

        if module.isModuleDef then
          synthesizedDefinitionsCache += module.companionModule -> (definition -> true)
        synthesizedDefinitionsCache += module -> (definition -> true)
        synthesizedDefinitionsCache += definition.binding -> (definition -> true)
        definition.init foreach { synthesizedDefinitionsCache += _ -> (definition -> true) }
        definition.impls foreach { synthesizedDefinitionsCache += _ -> (definition -> true) }
        definition -> true
      })
    })
    synthesizedDefinition
  end synthesizedModule

  def synthesizedDefinitions(symbol: Symbol): Option[SynthesizedDefinitions] =
    if !(symbol.flags is Flags.Synthetic) && !(symbol.flags is Flags.Artifact) || (symbol.name startsWith names.block) then
      if !symbol.isModuleDef && (symbol.isField || symbol.isMethod) then
        Some(synthesizedValOrDef(symbol))
      else if symbol.isModuleDef then
        Some(synthesizedModule(symbol))
      else
        None
    else
      None

  def synthesizedStatement(symbol: Symbol): Option[SynthesizedStatements] =
    synthesizedStatementsCache.get(symbol).flatten

  def synthesizedStatement(module: Symbol, peer: Symbol, index: Int): Option[SynthesizedStatements] =
    synthesizedStatementsCache.getOrElse((module, peer, index), {
      if peer != defn.AnyClass then
        val name = s"<${names.placedStatement} $index of ${fullName(peer)}>"
        val universalValues = synthesizedPlacedValues(module, defn.AnyClass).symbol
        val placedValues = synthesizedPlacedValues(module, peer).symbol
        val unaryProcedureType = MethodType(List.empty)(_ => List.empty, _ => TypeRepr.of[Unit])

        synthesizedStatementsCache.getOrElse((module, peer, index), {
          val binding = universalValues.declaredField(name) orElse:
            newMethod(universalValues, name, unaryProcedureType, Flags.Synthetic, Symbol.noSymbol)

          val impl = placedValues.declaredField(name) orElse:
            newMethod(placedValues, name, unaryProcedureType, Flags.Synthetic | Flags.Override, Symbol.noSymbol)

          val statement = Some(SynthesizedStatements(binding, List(impl)))
          synthesizedStatementsCache += (module, peer, index) -> statement
          synthesizedStatementsCache += binding -> (statement -> true)
          synthesizedStatementsCache += impl -> (statement -> true)
          statement
        })
      else
        synthesizedStatementsCache += (module, peer, index) -> None
        None
    })

  def synthesizeMember(symbol: Symbol): Boolean =
    isMultitierNestedPath(symbol.maybeOwner) &&
    (symbol.isTerm && !symbol.isModuleDef && !symbol.isParamAccessor || (symbol.isModuleDef && symbol.isClassDef))

  def synthesizedPlacedValues(symbol: Symbol): Option[SynthesizedPlacedValues] =
    synthesizedPlacedValuesCache.get(symbol) map: (synthesizedPlacedValues, _) =>
      synthesizedPlacedValues

  def synthesizedPlacedValues(symbol: Symbol, peer: Symbol): SynthesizedPlacedValues =
    val module = if symbol.moduleClass.exists then symbol.moduleClass else symbol
    val preprocessedTree = symbolPreprocessedTree(module)

    val cachedSynthesizedPlacedValues =
      synthesizedPlacedValuesCache.get(module, peer) collect:
        case (synthesizedPlacedValues, hasPreprocessedTree) if preprocessedTree.isEmpty || hasPreprocessedTree => synthesizedPlacedValues

    cachedSynthesizedPlacedValues getOrElse:
      val name = fullName(module)
      val mangledName = mangledSymbolName(module)
      val form = implementationForm(module)
      val separator = if module.isType && !module.isPackageDef && !module.isModuleDef then "#" else "."

      val (parents, selfType) =
        if isMultitierModule(module) then
          val moduleThisType = ThisType(module)
          val baseClasses = module.typeRef.baseClasses.toSet

          val inheritedPlacedValues =
            moduleThisType.baseClasses.tail.reverseIterator flatMap: parent =>
              Option.when(isMultitierModule(parent)):
                moduleThisType.select(synthesizedPlacedValues(parent, defn.AnyClass).symbol)

          val (parentPlacedValues, selfTypePlacedValues) = inheritedPlacedValues partition:
            baseClasses contains _.typeSymbol.owner

          val parents =
            TypeRepr.of[Object] :: (
              if peer == defn.AnyClass then (parentPlacedValues ++ Iterator(types.placedValues)).toList
              else synthesizedPlacedValues(module, defn.AnyClass).symbol.typeRef :: parentPlacedValues.toList)

          val selfType =
            Option.when(selfTypePlacedValues.hasNext):
              selfTypePlacedValues.foldLeft(selfTypePlacedValues.next) { AndType(_, _) }

          (parents, selfType)
        else
          (List(TypeRepr.of[Object]), None)

      if peer == defn.AnyClass then
        SymbolMutator.getOrErrorAndAbort.invalidateMemberCaches(module)

      val cachedSynthesizedPlacedValues =
        synthesizedPlacedValuesCache.get(module, peer) collect:
          case (synthesizedPlacedValues, hasPreprocessedTree) if preprocessedTree.isEmpty || hasPreprocessedTree => synthesizedPlacedValues

      cachedSynthesizedPlacedValues getOrElse:
        val symbol = syntheticTrait(
          module,
          if peer == defn.AnyClass then s"<${names.placedValues} of $form $name>" else s"<${names.placedValues} on $name$separator${peer.name}>",
          if peer == defn.AnyClass then mangledName else s"$mangledName$$${peer.name}",
          parents,
          selfType,
          noInits = peer != defn.AnyClass,
          enterSymbol = preprocessedTree.isDefined): symbol =>
            val placedValues = SynthesizedPlacedValues(symbol, module, peer, parents)
            if module.isModuleDef then
              synthesizedPlacedValuesCache += (module.companionModule, peer) -> (placedValues -> preprocessedTree.isDefined)
            synthesizedPlacedValuesCache += (module, peer) -> (placedValues -> preprocessedTree.isDefined)
            synthesizedPlacedValuesCache += symbol -> (placedValues -> preprocessedTree.isDefined)

            def collectDeclarations(impls: List[Symbol]) =
              impls collect { case impl if impl.owner == symbol => impl }

            val indices = mutable.Map.empty[Symbol, Int]

            val declarations =
              preprocessedTree match
                case Some(ClassDef(_, _, _, _, body)) =>
                  body flatMap:
                    case stat: Definition if synthesizeMember(stat.symbol) =>
                      synthesizedDefinitions(stat.symbol).fold(List.empty):
                        case SynthesizedDefinitions(_, binding, init, setter, impls) =>
                          collectDeclarations(binding :: init.toList ++ setter.toList ++ impls)
                    case statement: Term =>
                      val statementPeer = PlacementInfo(statement.tpe.resultType).fold(defn.AnyClass) { _.peerType.typeSymbol }
                      if peer == defn.AnyClass || peer == statementPeer then
                        val index = indices.getOrElse(statementPeer, 0)
                        indices += statementPeer -> (index + 1)
                        synthesizedStatement(module, statementPeer, index).toList flatMap: statement =>
                          collectDeclarations(statement.binding :: statement.impls)
                      else
                        List.empty
                    case _ =>
                      List.empty
                case _ =>
                  List.empty

            val decls =
              if declarations.isEmpty then
                module.declarations flatMap: decl =>
                  if synthesizeMember(decl) then
                    synthesizedDefinitions(decl).fold(List.empty):
                      case SynthesizedDefinitions(_, binding, init, setter, impls) =>
                        collectDeclarations(binding :: init.toList ++ setter.toList ++ impls)
                  else
                    List.empty
              else
                declarations

            if peer == defn.AnyClass &&
               (module.owner hasAncestor isMultitierModule) &&
               (parents forall { _.typeSymbol.maybeOwner.maybeOwner != symbol.maybeOwner.maybeOwner }) then
              val placedValues = synthesizedPlacedValues(module.owner, defn.AnyClass).symbol
              val name = s"<${names.outerPlacedValues} of ${implementationForm(module.owner)} ${fullName(module.owner)}>"
              newVal(symbol, name, placedValues.typeRef, Flags.ParamAccessor, Symbol.noSymbol) :: decls
            else
              decls
        end symbol

        val (paramNames, paramTypes) = (symbol.declaredFields collect { case symbol if symbol.isParamAccessor => symbol.name -> symbol.info }).unzip
        if paramNames.nonEmpty then
          val tpe = MethodType(paramNames)(_ => paramTypes, _ => symbol.typeRef)
          SymbolMutator.getOrErrorAndAbort.setInfo(symbol.primaryConstructor, tpe)

        SynthesizedPlacedValues(symbol, module, peer, parents)
  end synthesizedPlacedValues
end PlacedValueSynthesis
