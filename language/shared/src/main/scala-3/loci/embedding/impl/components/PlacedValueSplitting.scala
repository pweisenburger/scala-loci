package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.mutable

@experimental
trait PlacedValueSplitting:
  this: Component & Commons & Placements & NonPlacements & Peers & PlacedTransformations & PlacedStatements & PlacedValueSynthesis =>
  import quotes.reflect.*

  private def erasedBody(tpe: TypeRepr)(owner: Symbol) =
    if tpe =:= TypeRepr.of[Unit] then
      Literal(UnitConstant())
    else if tpe <:< TypeRepr.of[Nothing] then
      val symbol = newMethod(owner, "nullOf", PolyType(List("T"))(_ => List(TypeBounds.empty), _.param(0)), Flags.Synthetic, Symbol.noSymbol)
      val definition = DefDef(symbol, argss => Some(Literal(NullConstant()).select(symbols.asInstanceOf).appliedToTypeTrees(List(TypeIdent(argss.head.head.symbol)))))
      Block(List(definition), Ref(symbol).appliedToType(tpe))
    else
      Literal(NullConstant()).select(symbols.asInstanceOf).appliedToType(tpe)

  private def rhssByPeers(stat: Statement) =
    def peer =
      PlacementInfo(stat.symbol.info.widenTermRefByName.resultType).fold(defn.AnyClass) { _.peerType.typeSymbol }

    def rhssByPeers(rhs: Option[Term]) =
      rhs.fold(Map(peer -> None)): rhs =>
        val rhssByPeers =
          extractPlacementBodies(rhs) flatMap: (body, tpe) =>
            tpe.fold(Some(defn.AnyClass -> Some(body))): tpe =>
              PlacementInfo(tpe) map: placementInfo =>
                placementInfo.peerType.typeSymbol -> Some(body)
        rhssByPeers.toMap

    stat match
      case PlacedStatement(ValDef(_, _, rhs))  => rhssByPeers(rhs)
      case PlacedStatement(DefDef(_, _, _, rhs)) => rhssByPeers(rhs)
      case NonPlacedStatement(ValDef(_, _, rhs)) => rhssByPeers(rhs)
      case NonPlacedStatement(DefDef(_, _, _, rhs)) => rhssByPeers(rhs)
      case ValDef(_, _, rhs) => Map(defn.AnyClass -> rhs)
      case DefDef(_, _, _, rhs) => Map(defn.AnyClass -> rhs)
      case _ => Map.empty
  end rhssByPeers

  private def synthesizePlacedDefinition(impl: Symbol, stat: Statement, module: Symbol, rhss: Map[Symbol, Option[Term]]): ValDef | DefDef =
    val rhs = synthesizedPlacedValues(impl.owner) flatMap: placedValues =>
      rhss.get(placedValues.peer)

    val tpe = impl.info.resultType.substituteParamRefsByTermRefs(impl)

    val synthesizedBody = rhs.fold(Some(erasedBody(tpe)(impl))):
      _ map: rhs =>
        val body =
          if tpe =:= TypeRepr.of[Unit] && !(rhs.tpe =:= TypeRepr.of[Unit]) then
            rhs match
              case Lambda(_, _) => Block(List(rhs), Literal(UnitConstant()))
              case Block(statements, expr) => Block.copy(rhs)(statements :+ expr, Literal(UnitConstant()))
              case _ => Block(List(rhs), Literal(UnitConstant()))
          else
            rhs
        body.changeOwner(impl)

    if impl.isMethod then
      def body(paramss: List[List[Tree]]) = synthesizedBody map:
        _.substituteRefs((stat.symbol.paramSymss.flatten lazyZip (paramss flatMap { _ map { _.symbol } })).toMap, impl)
      DefDef(impl, body)
    else
      ValDef(impl, synthesizedBody)
  end synthesizePlacedDefinition

  def split(module: ClassDef): ClassDef =
    val indices = mutable.Map.empty[Symbol, Int]

    val universalPlacedValues = synthesizedPlacedValues(module.symbol, defn.AnyClass).symbol
    val universalPlacedValuesLocalDummy = SymbolMutator.getOrErrorAndAbort.createLocalDummy(universalPlacedValues)

    extension (self: Map[Symbol, List[Statement]])
      inline def prepended(symbol: Symbol)(stats: Statement*) =
        self + (symbol -> (stats.toList ++ self.getOrElse(symbol, List.empty)))

    val placedBodies = module.body.foldLeft(Map.empty[Symbol, List[Statement]]):
      case (bodies, stat @ (_: ValDef | _: DefDef)) if synthesizeMember(stat.symbol) =>
        synthesizedDefinitions(stat.symbol).fold(bodies): definitions =>
          val rhss =
            if stat.symbol.flags is Flags.Deferred then
              Map(defn.AnyClass -> None)
            else if definitions.binding.hasAnnotation(symbols.deferred) || definitions.binding.getter.hasAnnotation(symbols.deferred) then
              Map.empty
            else
              rhssByPeers(stat)

          val bodiesWithBinding = definitions match
            case SynthesizedDefinitions(_, binding, None, _, _) =>
              bodies.prepended(binding.owner)(synthesizePlacedDefinition(binding, stat, module.symbol, rhss))
            case SynthesizedDefinitions(_, binding, Some(init), _, _) =>
              bodies.prepended(binding.owner)(ValDef(binding, Some(Ref(init).appliedToNone)))
                .prepended(init.owner)(synthesizePlacedDefinition(init, stat, module.symbol, rhss))

          val bodiesWithBindingAndSetter = definitions match
            case SynthesizedDefinitions(_, _, _, Some(setter), _) =>
              bodiesWithBinding.prepended(setter.owner)(DefDef(setter, _ => Some(Literal(UnitConstant()))))
            case _ =>
              bodiesWithBinding

          definitions.impls.foldLeft(bodiesWithBindingAndSetter): (bodies, impl) =>
            bodies.prepended(impl.owner)(synthesizePlacedDefinition(impl, stat, module.symbol, rhss))

      case (bodies, stat: ClassDef) if synthesizeMember(stat.symbol) =>
        synthesizedDefinitions(stat.symbol).fold(bodies): nestedModule =>
          bodies.prepended(nestedModule.binding.owner)(ValDef(nestedModule.binding, None))

      case (bodies, term: Term) =>
        val placementInfo = PlacementInfo(term.tpe.resultType)
        val peer = placementInfo.fold(defn.AnyClass) { _.peerType.typeSymbol }
        val index = indices.getOrElse(peer, 0)
        indices += peer -> (index + 1)

        def extractPlacementBody(term: Term) = extractPlacementBodies(term) match
          case List(body -> _) => body
          case _ => term

        val bodiesUniversalValues =
          if !placementInfo.isDefined then
            bodies.prepended(universalPlacedValues)(term.changeOwner(universalPlacedValuesLocalDummy))
          else if peer == defn.AnyClass then
            bodies.prepended(universalPlacedValues)(extractPlacementBody(term).changeOwner(universalPlacedValuesLocalDummy))
          else
            synthesizedStatement(module.symbol, peer, index).fold(bodies): statement =>
              bodies.prepended(universalPlacedValues)(DefDef(statement.binding, _ => Some(Literal(UnitConstant()))), Ref(statement.binding).appliedToNone)

        if peer == defn.AnyClass then
          bodiesUniversalValues
        else
          synthesizedStatement(module.symbol, peer, index).fold(bodiesUniversalValues): statement =>
            val rhs = extractPlacementBody(term) match
              case Block(statements, expr) if expr.tpe.typeSymbol != defn.UnitClass =>
                Block(statements :+ expr, Literal(UnitConstant()))
              case expr if expr.tpe.typeSymbol != defn.UnitClass =>
                Block(List(expr), Literal(UnitConstant()))
              case expr =>
                expr
            statement.impls.foldLeft(bodiesUniversalValues): (bodies, impl) =>
              bodies.prepended(impl.owner)(DefDef(impl, _ => Some(rhs.changeOwner(impl))))

      case (bodies, _) =>
        bodies
    end placedBodies

    val placedBody = PeerInfo.ofModule(module.symbol) map: peerInfo =>
      val SynthesizedPlacedValues(placedValues, _, _, parents) = synthesizedPlacedValues(module.symbol, peerInfo.peerType.typeSymbol)
      val tpe = placedValues.typeRef
      val params = placedValues.declaredFields collect { case symbol if symbol.isParamAccessor => ValDef(symbol, None) }
      val classDef = ClassDef(placedValues, parents map { parent => TypeTree.of(using parent.asType) }, params ++ placedBodies.getOrElse(placedValues, List.empty).reverse)
      ClassDef.copy(classDef)(classDef.name, DefDef(classDef.constructor.symbol, _ => None), classDef.parents, classDef.self, classDef.body)

    def eraseBody(stat: Definition, term: Term) =
      transformBody(term, stat.symbol.info.resultType, stat.symbol): (_, tpe, owners) =>
        erasedBody(owners.foldLeft(tpe) { _.substituteParamRefsByTermRefs(_) })(owners.head)

    val body = module.body flatMap:
      case stat @ ValDef(name, tpt, rhs) if !stat.symbol.isModuleDef =>
        Some(ValDef.copy(stat)(name, tpt, rhs map { eraseBody(stat, _) }))
      case stat @ DefDef(name, paramss, tpt, rhs) =>
        if stat.symbol.isFieldAccessor then
          if stat.symbol.getter.hasAnnotation(symbols.deferred) then
            Some(DefDef.copy(stat)(name, paramss, tpt, rhs map { _ => Literal(UnitConstant()) }))
          else
            Some(stat)
        else
          Some(DefDef.copy(stat)(name, paramss, tpt, rhs map { eraseBody(stat, _) }))
      case stat: ClassDef if stat.symbol.isModuleDef && !isMultitierModule(stat.symbol) =>
        Some(split(stat))
      case stat: Definition =>
        Some(stat)
      case stat =>
        None

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, body ++ placedBody)
  end split
end PlacedValueSplitting

