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
  this: Component & Commons & Annotations & SymbolTrees & Placements & NonPlacements & Peers =>
  import quotes.reflect.*

  case class SynthesizedPlacedValues(symbol: Symbol, module: Symbol, peer: Symbol, parents: List[TypeRepr])
  case class SynthesizedDefinitions(original: Symbol, binding: Symbol, init: Option[Symbol], impls: List[Symbol])
  case class SynthesizedStatements(binding: Symbol, impls: List[Symbol])

  private val synthesizedDefinitionsCache = PlacedValueSynthesis.synthesizedDefinitionsCache match
    case cache: mutable.Map[Symbol, SynthesizedDefinitions] @unchecked => cache
  private val synthesizedStatementsCache = PlacedValueSynthesis.synthesizedStatementsCache match
    case cache: mutable.Map[(Symbol, Symbol, Int) | Symbol, Option[SynthesizedStatements]] @unchecked => cache
  private val synthesizedPlacedValuesCache = PlacedValueSynthesis.synthesizedPlacedValuesCache match
    case cache: mutable.Map[(Symbol, Symbol) | Symbol, SynthesizedPlacedValues] @unchecked => cache

  private def mangledSymbolName(symbol: Symbol) =
    f"loci$$${s"${implementationForm(symbol)} ${fullName(symbol)}".hashCode}%08x"

  private def implementationForm(symbol: Symbol) =
    if symbol.flags is Flags.Module then "object"
    else if symbol.flags is Flags.Trait then "trait"
    else "class"

  private def syntheticTrait(owner: Symbol, name: String, mangledName: String, parents: List[TypeRepr], noInits: Boolean)(decls: Symbol => List[Symbol]) =
    owner.typeMember(name) orElse owner.typeMember(mangledName) orElse:
      val flags = Flags.Synthetic | Flags.Trait | (if noInits then Flags.NoInits else Flags.EmptyFlags)
      val symbol = newClass(owner, if canMakeTargetName then name else mangledName, flags, parents, decls, selfType = None)
      tryMakeTargetName(symbol, mangledName)
      SymbolMutator.getOrErrorAndAbort.enter(owner, symbol)
      symbol

  private def copyAnnotations(from: Symbol, to: Symbol, decrementContextResultCount: Boolean) =
    def updateSymbolAnnotationWithTree(symbol: Symbol, tree: Tree): Unit =
      SymbolMutator.get.fold(
        report.warning("Annotations in multitier modules are ignored with current compiler version.", from.annotations.head.posInUserCode)):
        _.updateAnnotationWithTree(symbol, tree)

    from.annotations foreach:
      case tree @ Apply(fun, List(arg @ Literal(IntConstant(count))))
        if decrementContextResultCount &&
           fun.symbol.isClassConstructor &&
           fun.symbol.owner == symbols.contextResultCount =>
        if count > 1 then
          updateSymbolAnnotationWithTree(to, Apply.copy(tree)(fun, List(Literal.copy(arg)(IntConstant(count - 1)))))
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

  private object multitierModuleTypeUnlifter extends TypeMap(quotes):
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
        tpe.select(synthesizedPlacedValues(symbol, defn.AnyClass).symbol)

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
  end multitierModuleTypeUnlifter

  private def synthesizedValOrDef(symbol: Symbol): SynthesizedDefinitions = synthesizedDefinitionsCache.getOrElse(symbol, {
    val placedName = s"<placed ${symbol.name} of ${fullName(symbol.owner)}>"
    val (universalName, info, peer) =
      symbol.info match
        case MethodType(List(paramName), List(paramType), resultType)
          if resultType.typeSymbol == defn.UnitClass &&
             symbol.isFieldAccessor &&
             (symbol.name endsWith "_=") =>
          val name =
            if symbol.flags is Flags.Private then
              s"<placed private ${symbol.name.dropRight(2)} of ${fullName(symbol.owner)}>_="
            else
              symbol.name
          val (info, _) = erasePlacementAndNonPlacementType(paramType)
          (name, MethodType(List(paramName))(_ => List(info), _ => resultType), defn.AnyClass)
        case tpe =>
          if isMultitierModule(symbol) then
            (symbol.name, multitierModuleTypeUnlifter.transform(tpe), defn.AnyClass)
          else
            val name = if symbol.flags is Flags.Private then s"<placed private ${symbol.name} of ${fullName(symbol.owner)}>" else symbol.name
            val (info, peer) = erasePlacementAndNonPlacementType(symbol.info)
            (name, if hasSyntheticMultitierContextArgument(symbol) then dropLastArgumentList(info) else info, peer)

    val universalValues = synthesizedPlacedValues(symbol.owner, defn.AnyClass).symbol
    val placedValues = synthesizedPlacedValues(symbol.owner, peer).symbol

    synthesizedDefinitionsCache.getOrElse(symbol, {
      val universalOnly = peer == defn.AnyClass || (symbol.flags is Flags.Deferred)
      val flags = if universalOnly then symbol.flags else symbol.flags &~ Flags.PrivateLocal
      val decrementContextResultCount = info != symbol.info

      val universal = universalValues.fieldMember(universalName) orElse:
        val universal = newVal(universalValues, universalName, info, flags, Symbol.noSymbol)
        copyAnnotations(symbol, universal, decrementContextResultCount)
        universal

      val definition =
        if !universalOnly then
          if symbol.isMethod then
            val placed = placedValues.methodMember(universalName) find { _.info =:= info } getOrElse:
              val placed = newMethod(placedValues, universalName, info, flags | Flags.Synthetic | Flags.Override, Symbol.noSymbol)
              copyAnnotations(symbol, placed, decrementContextResultCount)
              placed
            SynthesizedDefinitions(symbol, universal, None, List(placed))
          else
            val methodType = MethodType(List.empty)(_ => List.empty, _ => info)

            val universalInit = universalValues.fieldMember(placedName) orElse:
              newMethod(universalValues, placedName, methodType, Flags.Synthetic, Symbol.noSymbol)

            val placedInit = placedValues.fieldMember(placedName) orElse:
              val placedInit = newMethod(placedValues, placedName, methodType, Flags.Synthetic | Flags.Override, Symbol.noSymbol)
              copyAnnotations(symbol, placedInit, decrementContextResultCount)
              placedInit

            SynthesizedDefinitions(symbol, universal, Some(universalInit), List(placedInit))
        else
          SynthesizedDefinitions(symbol, universal, None, List.empty)
      end definition

      synthesizedDefinitionsCache += symbol -> definition
      synthesizedDefinitionsCache += definition.binding -> definition
      definition.init foreach { synthesizedDefinitionsCache += _ -> definition }
      definition.impls foreach { synthesizedDefinitionsCache += _ -> definition }
      definition
    })
  })

  private def synthesizedModule(symbol: Symbol): SynthesizedDefinitions = synthesizedDefinitionsCache.getOrElse(symbol, {
    val module = if symbol.moduleClass.exists then symbol.moduleClass else symbol
    val modulePlacedValues = synthesizedPlacedValues(module, defn.AnyClass).symbol
    val ownerPlacedValues = synthesizedPlacedValues(module.owner, defn.AnyClass).symbol
    synthesizedDefinitionsCache.getOrElse(module, {
      val binding = ownerPlacedValues.fieldMember(module.companionModule.name) orElse:
        newVal(ownerPlacedValues, module.companionModule.name, modulePlacedValues.typeRef, Flags.Deferred | Flags.Lazy | Flags.StableRealizable, Symbol.noSymbol)
      val definition = SynthesizedDefinitions(module, binding, None, List.empty)
      if module.isModuleDef then
        synthesizedDefinitionsCache += module.companionModule -> definition
      synthesizedDefinitionsCache += module -> definition
      synthesizedDefinitionsCache += definition.binding -> definition
      definition.init foreach { synthesizedDefinitionsCache += _ -> definition }
      definition.impls foreach { synthesizedDefinitionsCache += _ -> definition }
      definition
    })
  })

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
        val name = s"<placed statement ${index} of ${fullName(peer)}>"
        val universalValues = synthesizedPlacedValues(module, defn.AnyClass).symbol
        val placedValues = synthesizedPlacedValues(module, peer).symbol
        val unaryProcedureType = MethodType(List.empty)(_ => List.empty, _ => TypeRepr.of[Unit])

        synthesizedStatementsCache.getOrElse((module, peer, index), {
          val binding = universalValues.fieldMember(name) orElse:
            newMethod(universalValues, name, unaryProcedureType, Flags.Synthetic, Symbol.noSymbol)

          val impl = placedValues.fieldMember(name) orElse:
            newMethod(placedValues, name, unaryProcedureType, Flags.Synthetic | Flags.Override, Symbol.noSymbol)

          val statement = Some(SynthesizedStatements(binding, List(impl)))
          synthesizedStatementsCache += (module, peer, index) -> statement
          synthesizedDefinitionsCache += binding -> statement
          synthesizedDefinitionsCache += impl -> statement
          statement
        })
      else
        synthesizedStatementsCache += (module, peer, index) -> None
        None
    })

  def synthesizedPlacedValues(symbol: Symbol): Option[SynthesizedPlacedValues] =
    synthesizedPlacedValuesCache.get(symbol)

  def synthesizedPlacedValues(symbol: Symbol, peer: Symbol): SynthesizedPlacedValues =
    val module = if symbol.moduleClass.exists then symbol.moduleClass else symbol
    synthesizedPlacedValuesCache.getOrElse((module, peer), {
      val name = fullName(module)
      val mangledName = mangledSymbolName(module)
      val form = implementationForm(module)
      val separator = if module.isType && !module.isPackageDef && !module.isModuleDef then "#" else "."

      def inheritedParentPlacedValues =
        module.typeRef.baseClasses.tail flatMap: parent =>
          if isMultitierModule(parent) then
            val symbols =
              if peer == defn.AnyClass then List(defn.AnyClass)
              else parent.typeMember(peer.name).fold(List(defn.AnyClass)) { symbol => List(symbol, defn.AnyClass) }
            symbols map: symbol =>
              ThisType(module).select(synthesizedPlacedValues(parent, symbol).symbol)
          else
            List.empty

      def declaredParentPlacedValues =
        PeerInfo(ThisType(module).select(peer)).toList flatMap:
          _.parents collect:
            case parent @ TypeRef(qualifier, _) if PeerInfo(parent).isDefined =>
              qualifier.select(synthesizedPlacedValues(qualifier.typeSymbol, parent.typeSymbol).symbol)

      val parents =
        TypeRepr.of[Object] :: (
          if !isMultitierModule(module) then List.empty
          else if peer == defn.AnyClass then declaredParentPlacedValues ++ inheritedParentPlacedValues :+ types.placedValues
          else synthesizedPlacedValues(module, defn.AnyClass).symbol.typeRef :: declaredParentPlacedValues ++ inheritedParentPlacedValues)

      if peer == defn.AnyClass then
        SymbolMutator.getOrErrorAndAbort.invalidateMemberCaches(module)

      synthesizedPlacedValuesCache.getOrElse((module, peer), {
        val symbol = syntheticTrait(
          module,
          if peer == defn.AnyClass then s"<placed values of $form $name>" else s"<placed values on $name$separator${peer.name}>",
          if peer == defn.AnyClass then mangledName else s"$mangledName$$${peer.name}",
          parents,
          noInits = peer != defn.AnyClass): symbol =>
            val placedValues = SynthesizedPlacedValues(symbol, module, peer, parents)
            if module.isModuleDef then
              synthesizedPlacedValuesCache += (module.companionModule, peer) -> placedValues
            synthesizedPlacedValuesCache += (module, peer) -> placedValues
            synthesizedPlacedValuesCache += symbol -> placedValues

            inline def collectDeclarations(impls: List[Symbol]) =
              impls collect { case impl if impl.owner == symbol => impl }

            val indices = mutable.Map.empty[Symbol, Int]

            val declarations =
              symbolTree(module) match
                case Some(ClassDef(_, _, _, _, body)) =>
                  body flatMap:
                    case stat: Definition if !stat.symbol.isModuleDef || (stat.symbol.isModuleDef && stat.symbol.isClassDef) =>
                      synthesizedDefinitions(stat.symbol).fold(List.empty): definitions =>
                        collectDeclarations(definitions.binding :: definitions.init.toList ++ definitions.impls)
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
                  if !decl.isModuleDef || (decl.isModuleDef && decl.isClassDef) then
                    synthesizedDefinitions(decl).fold(List.empty): definitions =>
                      collectDeclarations(definitions.binding :: definitions.init.toList ++ definitions.impls)
                  else
                    List.empty
              else
                declarations

            if peer == defn.AnyClass &&
               (module.owner hasAncestor isMultitierModule) &&
               (parents forall { _.typeSymbol.maybeOwner.maybeOwner != symbol.maybeOwner.maybeOwner }) then
              val placedValues = synthesizedPlacedValues(module.owner, defn.AnyClass).symbol
              val name = s"<outer placed values of ${implementationForm(module.owner)} ${fullName(module.owner)}>"
              newVal(symbol, name, placedValues.typeRef, Flags.ParamAccessor, Symbol.noSymbol) :: decls
            else
              decls
        end symbol

        val (names, tpes) = (symbol.declaredFields collect { case symbol if symbol.isParamAccessor => symbol.name -> symbol.info }).unzip
        if names.nonEmpty then
          val tpe = MethodType(names)(_ => tpes, _ => symbol.typeRef)
          SymbolMutator.getOrErrorAndAbort.setInfo(symbol.primaryConstructor, tpe)

        SynthesizedPlacedValues(symbol, module, peer, parents)
      })
    })
end PlacedValueSynthesis
