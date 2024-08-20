package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.quoted.*

@experimental
trait PlacedStatements:
  this: Component & Commons & ErrorReporter & Placements & Peers & PlacedTransformations =>
  import quotes.reflect.*

  private object PlacementCallBindingArtifact:
    def unapply(term: Term): Option[(List[Definition], Term)] = term match
      case Inlined(Some(call), bindings, body)
          if call.symbol.hasAncestor(symbols.on, symbols.on.companionModule.moduleClass) =>
        Some(bindings, body)
      case _ =>
        None

  private object PlacementCallContextEvidenceArtifact:
    def unapply(term: Term): Option[(Definition, Term)] = term match
      case Inlined(_, List(), block @ Block((evidence: ValDef) :: statements, expr))
          if (evidence.symbol.flags is Flags.Synthetic) &&
             !(evidence.tpt.tpe =:= TypeRepr.of[Nothing]) &&
             evidence.tpt.tpe <:< types.context =>
        if statements.nonEmpty then
          Some(evidence, Block.copy(block)(statements, expr))
        else
          Some(evidence, expr)
      case _ =>
        None

  private object PlacementCallArtifact:
    def unapply(term: Term): Option[(List[Definition], Term)] = term match
      case PlacementCallBindingArtifact(bindings, expr) => Some(bindings, expr)
      case PlacementCallContextEvidenceArtifact(binding, expr) => Some(List(binding), expr)
      case _ => None

  private object PlacementErasedArtifact:
    def unapply(term: Term): Option[Term] = term match
      case Block(List(statement @ Inlined(_, _, _)), erased: TypeApply)
          if erased.symbol == symbols.erased || erased.symbol == symbols.erasedArgs =>
        Some(statement)
      case _ =>
        None

  private object PlacedExpression:
    def unapply(term: Term): Some[(List[Definition], Term)] = Term.safeTryBetaReduce(term) match
      case PlacementErasedArtifact(PlacementCallArtifact(bindings, expr)) => Term.safeTryBetaReduce(expr) match
        case PlacedExpression(nestedBindings, expr) => Some((bindings ++ nestedBindings) -> expr)
      case PlacementCallArtifact(bindings, expr) => Term.safeTryBetaReduce(expr) match
        case PlacedExpression(nestedBindings, expr) => Some((bindings ++ nestedBindings) -> expr)
      case term @ Apply(select @ Select(PlacedExpression(bindings, expr), names.apply), List(arg)) =>
        Term.safeBetaReduce(expr.select(select.symbol).appliedTo(arg)) match
          case Some(PlacedExpression(nestedBindings, expr)) => Some((bindings ++ nestedBindings) -> expr)
          case _ => Some(List.empty -> term)
      case expr =>
        Some(List.empty -> expr)

  private object PlacementCompounds:
    def unapply(term: Term): Option[(List[Definition], List[(PlacementInfo, Term)])] = Term.safeTryBetaReduce(term) match
      case Inlined(Some(call), bindings, Block(stats, erased: TypeApply))
          if call.symbol.hasAncestor(symbols.and.owner) &&
             stats.nonEmpty &&
             bindings.nonEmpty &&
             (bindings forall { _.symbol.info.typeSymbol == symbols.lowestCommonSuperType }) &&
             (erased.symbol == symbols.erased || erased.symbol == symbols.erasedArgs) =>
        stats.foldLeft[Option[(List[Definition], List[(PlacementInfo, Term)])]](Some(bindings, List.empty)):
          case (Some(bindings, compounds), Inlined(_, List(), closure @ Lambda(List(arg), body)))
            if !(arg.tpt.tpe =:= TypeRepr.of[Nothing]) &&
               arg.tpt.tpe <:< types.context &&
               arg.symbol.isImplicit =>
            body match
              case PlacementCompounds(nestedBindings, nestedCompounds) =>
                val flattenedNestedCompounds = nestedCompounds map: (placementInfo, compound) =>
                  placementInfo -> compound.changeOwner(arg.symbol.owner.owner)
                Some(bindings ++ nestedBindings, compounds ++ flattenedNestedCompounds)
              case _ =>
                PlacementInfo(closure.tpe) map: placementInfo =>
                  (bindings, compounds :+ placementInfo -> closure)
          case _ =>
            None
      case Apply(select @ Select(Inlined(call, bindings, expr @ Lambda(_, _)), names.apply), List(arg)) =>
        Term.safeBetaReduce(expr.select(select.symbol).appliedTo(arg)) match
          case Some(expr) => Inlined(call, bindings, expr) match
            case PlacementCompounds(bindings, compounds) => Some(bindings, compounds)
            case _ => None
          case _ => None
      case _ =>
        None

  private def bindingsForPlacementConstructs(bindings: List[Definition]): (List[Definition], Boolean) =
    val placedContextProxyBindings = bindings collect:
      case binding @ ValDef(_, tpt, Some(Block(List(context @ ValDef("<synthetic context>", _, Some(erased))), expr)))
        if !(tpt.tpe =:= TypeRepr.of[Nothing]) &&
           tpt.tpe <:< types.placedContext &&
           erased.symbol == symbols.erased &&
           expr.symbol == context.symbol &&
           (context.symbol.flags is Flags.Synthetic) =>
        binding.symbol

    val placedContextProxies = placedContextProxyBindings.toSet

    val placementConstructBindings = bindings flatMap:
      // non-synthetic bindings for `placed` construct
      // (represented by the `Placement.Context[P]` argument that contains an `Placed.Context` term)
      case binding @ ValDef(_, tpt, Some(Apply(_, List(Typed(Repeated(List(expr), _), _)))))
        if !(tpt.tpe =:= TypeRepr.of[Nothing]) &&
           tpt.tpe <:< types.context &&
           !(expr.tpe =:= TypeRepr.of[Nothing]) &&
           expr.tpe <:< types.placedContext &&
           !(placedContextProxies contains expr.tpe.termSymbol) =>
        Some(Left(binding))

      // bindings for `on` construct
      // (represented by the `On[P] & Run[P, from]` prefix)
      case binding @ ValDef(_, tpt, _) =>
        binding.tpt.tpe match
          case AndType(left, right) if left.typeSymbol == symbols.on && right.typeSymbol == symbols.run => Some(Right(binding))
          case _ => None

      case _ =>
        None
    end placementConstructBindings

    (placementConstructBindings map { _.merge }, placementConstructBindings exists { _.isLeft })
  end bindingsForPlacementConstructs

  private def bindingsForPlacementConstructs(bindings: Iterable[List[Definition]]): (List[List[Definition]], Boolean) =
    val (placementConstructsBindings, hasNonSyntheticPlacedConstructBindings) = (bindings.toList map bindingsForPlacementConstructs).unzip
    (placementConstructsBindings, hasNonSyntheticPlacedConstructBindings contains true)

  private def cleanPlacementExpression(placementInfo: PlacementInfo, term: Term): (List[List[Definition]], Term) =
    val PlacedExpression(bindings, expr) = term

    val (compoundBindings, exprs) = expr match
      case PlacementCompounds(compoundBindings, compounds) =>
        val (bindings, exprs) = (compounds map cleanPlacementExpressionOrClosure).unzip
        (compoundBindings :: bindings.flatten, exprs)
      case _ =>
        (List.empty, List(expr))

    val erasedContext = Ref(symbols.erased).appliedToType(symbols.`embedding.on`.typeRef.appliedTo(placementInfo.canonicalType.typeArgs))
    (bindings :: compoundBindings) -> Block(exprs, erasedContext)
  end cleanPlacementExpression

  private def cleanPlacementExpressionOrClosure(placementInfo: PlacementInfo, expr: Term): (List[List[Definition]], Term) =
    expr match
      case block @ Lambda(List(arg), _)
        if !(arg.tpt.tpe =:= TypeRepr.of[Nothing]) &&
           arg.tpt.tpe <:< types.context &&
           arg.symbol.isImplicit =>
        val Block(List(lambda: DefDef), closure) = block: @unchecked
        val (bindings, body) = cleanPlacementExpression(placementInfo, lambda.rhs.get)
        bindings ->
          Block.copy(block)(
            List(DefDef.copy(lambda)(lambda.name, lambda.paramss, lambda.returnTpt, Some(body.changeOwner(lambda.symbol)))),
            closure)
      case _ =>
        val (bindings, body) = cleanPlacementExpression(placementInfo, expr)
        (bindings collectFirst { case binding :: _ => binding }).fold(bindings -> body): binding =>
          val peer = placementInfo.peerType.asPackedValueType
          val placement = symbols.`embedding.on`.typeRef.appliedTo(placementInfo.canonicalType.typeArgs).asPackedValueType
          val tpe = contextMethodType[Placement.Context[peer.Type], placement.Type]
          val block @ Block(List(lambda: DefDef), closure @ Closure(meth, _)) =
            Lambda(binding.symbol.owner, tpe, (symbol, _) => body.changeOwner(symbol)): @unchecked
          bindings ->
            Block.copy(block)(List(lambda), Closure.copy(closure)(meth, Some(placementInfo.canonicalType)))

  private def cleanPlacementSyntax(placementInfo: PlacementInfo, rhs: Term)(owner: Symbol): (List[List[Definition]], Term) =
    val (bindings, expr) = cleanPlacementExpressionOrClosure(placementInfo, rhs)
    bindings -> clearContextVariables(expr)(owner)

  private def cleanPlacementSyntax(placementInfo: PlacementInfo, rhs: Option[Term])(owner: Symbol): (List[List[Definition]], Option[Term]) =
    rhs.fold(List.empty -> None): rhs =>
      val (bindings, expr) = cleanPlacementSyntax(placementInfo, rhs)(owner)
      bindings -> Some(expr)

  private def cleanSpuriousPlacementSyntax(stat: Statement, rhs: Option[Term])(owner: Symbol): Option[Term] =
    def cleanSpuriousPlacementSyntax(rhs: Term): Term =
      val PlacedExpression(bindings, expr) = rhs

      val (placementConstructsBindings, _) = bindingsForPlacementConstructs(bindings)
      errorForExtraBindings(stat, placementConstructsBindings)

      expr match
        case block @ Lambda(_, _) if block.tpe.isContextFunctionType =>
          val Block(List(lambda: DefDef), closure) = block: @unchecked
          Block.copy(block)(
            List(DefDef.copy(lambda)(lambda.name, lambda.paramss, lambda.returnTpt, Some(cleanSpuriousPlacementSyntax(lambda.rhs.get).changeOwner(lambda.symbol)))),
            closure)
        case _ =>
          expr

    rhs map: rhs =>
      clearContextVariables(cleanSpuriousPlacementSyntax(rhs))(owner)
  end cleanSpuriousPlacementSyntax

  private def cleanSpuriousPlacementSyntax(stat: ValDef | DefDef): ValDef | DefDef =
    stat match
      case ValDef(name, tpt, rhs) => ValDef.copy(stat)(name, tpt, cleanSpuriousPlacementSyntax(stat, rhs)(stat.symbol))
      case DefDef(name, paramss, tpt, rhs) => DefDef.copy(stat)(name, paramss, tpt, cleanSpuriousPlacementSyntax(stat, rhs)(stat.symbol))

  private def placementType(stat: ValDef | DefDef, tpt: TypeTree) =
    PlacementInfo(stat.symbol.info.resultType) filter: placementInfo =>
      def pos = tpt match
        case Inferred() => stat.posInUserCode.firstCodeLine
        case _ => tpt.posInUserCode
      if placementInfo.valueType.isContextFunctionType then
        errorAndCancel(s"Placed type cannot be a context function type: ${placementInfo.valueType.safeShow}", pos)
      else if !placementInfo.canonical then
        val message = tpt match
          case Inferred() => "Placement type could not be inferred. Explicit type ascription required."
          case _ => "Invalid placement type."
        errorAndCancel(
          s"$message Expected type: ${placementInfo.showCanonical}" +
          s"${System.lineSeparator}Placement types are imported by: import loci.language.*", pos)
      placementInfo.canonical

  private def errorForExtraBindings(stat: Statement, placementConstructsBindings: List[Definition]): Unit =
    val accaptableBindingsCount = stat match
      case PlacedStatement(_) | _: Term => 1
      case _ =>  0
    placementConstructsBindings.drop(accaptableBindingsCount) foreach: binding =>
      val bindingPosition = binding.posInUserCode
      val pos = if bindingPosition == Position.ofMacroExpansion then stat.posInUserCode else bindingPosition
      errorAndCancel("Illegal use of multitier construct.", pos.firstCodeLine)

  private def errorForExtraBindings(stat: Statement, placementConstructsBindings: Iterable[List[Definition]]): Unit =
    placementConstructsBindings.iterator.zipWithIndex foreach: (placementConstructsBindings, index) =>
      if index == 0 || !canceled then
        errorForExtraBindings(stat, placementConstructsBindings)

  private def checkPeerType(stat: Statement, peerType: TypeRepr, module: ClassDef, statement: String, relation: String): Unit =
    if PeerInfo(peerType).isEmpty then
      errorAndCancel(
        s"$statement must be $relation a peer type but is $relation ${peerType.safeShow}",
        stat.posInUserCode.firstCodeLine)
    if peerType.typeSymbol != defn.AnyClass && !(peerType =:= ThisType(module.symbol).select(peerType.typeSymbol)) then
      errorAndCancel(
        s"$statement must be $relation a peer of module ${module.symbol.name} " +
        s"but is $relation peer ${peerType.safeShow}",
        stat.posInUserCode.firstCodeLine)

  private def statementTypeTreeInfo(stat: Statement) = stat match
    case ValDef(_, Inferred(), _) | DefDef(_, _, Inferred(), _) => (stat.posInUserCode.firstCodeLine, true)
    case ValDef(_, tpt, _) => (tpt.posInUserCode, false)
    case DefDef(_, _, tpt, _) => (tpt.posInUserCode, false)
    case _ => (stat.posInUserCode.firstCodeLine, false)

  private def checkPlacementType(stat: Statement, bindings: List[List[Definition]], placementInfo: PlacementInfo, module: ClassDef): Unit =
    val (statement, subjectiveStatement) = stat match
      case _: ValDef | _: DefDef => ("Placed definition", "Subjective placed definition")
      case _ => ("Placed statement", "Subjective placed statement")
    checkPeerType(stat, placementInfo.peerType, module, statement, "placed on")
    placementInfo.modality.subjectivePeerType foreach { checkPeerType(stat, _, module, subjectiveStatement, "subjective to") }

    val (placementConstructsBindings, hasNonSyntheticPlacedConstructBindings) = bindingsForPlacementConstructs(bindings)
    errorForExtraBindings(stat, placementConstructsBindings)

    val (pos, inferred) = statementTypeTreeInfo(stat)

    if inferred && (bindings.isEmpty || hasNonSyntheticPlacedConstructBindings) then
      errorAndCancel(s"Placed definitions without type ascription must be enclosed in a placed block: on[${placementInfo.peerType.safeShow(Printer.SafeTypeReprShortCode)}]", pos)
  end checkPlacementType

  private class SingletonTypeChecker(stat: Statement) extends TypeMap(quotes):
    override def transform(tpe: TypeRepr) = tpe match
      case _: TermRef if tpe.termSymbol hasAncestor isMultitierModule =>
        val (pos, _) = statementTypeTreeInfo(stat)
        errorAndCancel("Singleton types for values of multitier modules are not supported.", pos)
        tpe
      case _: NamedType =>
        tpe
      case _ =>
        super.transform(tpe)

  def normalizePlacedStatements(module: ClassDef): ClassDef =
    val body = module.body map:
      case stat @ ValDef(name, tpt, rhs) =>
        SingletonTypeChecker(stat).transform(tpt.tpe)
        placementType(stat, tpt).fold(cleanSpuriousPlacementSyntax(stat)): placementInfo =>
          val (bindings, expr) = cleanPlacementSyntax(placementInfo, rhs)(stat.symbol)
          checkPlacementType(stat, bindings, placementInfo, module)
          ValDef.copy(stat)(name, tpt, expr)

      case stat @ DefDef(name, paramss, tpt, rhs) =>
        SingletonTypeChecker(stat).transform(tpt.tpe)
        placementType(stat, tpt).fold(cleanSpuriousPlacementSyntax(stat)): placementInfo =>
          val (bindings, expr) = cleanPlacementSyntax(placementInfo, rhs)(stat.symbol)
          checkPlacementType(stat, bindings, placementInfo, module)
          if !placementInfo.modality.local then
            val nonSyntheticParamss =
              if hasSyntheticMultitierContextArgument(stat.symbol) then
                paramss.init
              else
                paramss
            nonSyntheticParamss foreach:
              case TypeParamClause(param :: _) if !canceled =>
                errorAndCancel("Non-local placed definitions cannot have type parameters.", param.posInUserCode)
              case TermParamClause(param :: _) if !canceled && param.symbol.isImplicit =>
                errorAndCancel("Non-local placed definitions cannot have context parameters.", param.posInUserCode)
              case _ =>
          DefDef.copy(stat)(name, paramss, tpt, expr)

      case stat: Term =>
        PlacementInfo(stat.tpe).fold(stat): placementInfo =>
          val (bindings, expr) = cleanPlacementSyntax(placementInfo, stat)(module.symbol)

          val (placementConstructsBindings, hasNonSyntheticPlacedConstructBindings) = bindingsForPlacementConstructs(bindings)
          errorForExtraBindings(stat, placementConstructsBindings)

          if bindings.isEmpty || hasNonSyntheticPlacedConstructBindings then
            errorAndCancel(s"Placed statements must be enclosed in a placed block: on[${placementInfo.peerType.safeShow(Printer.SafeTypeReprShortCode)}]", stat.posInUserCode.firstCodeLine)
          else if bindings.sizeIs > 1 then
            val compound = extractPlacementBodies(expr) match
              case (_, peer1) :: (_, peer2) :: _ => s": (on[${peer1.name}] <...>) and (on[${peer2.name}] <...>)"
              case _ => ""
            errorAndCancel(s"Placed statements cannot be compound placed expressions$compound. Consider splitting them into separate statements.", stat.posInUserCode.firstCodeLine)

          if placementInfo.modality.subjective then
            errorAndCancel("Placed statements cannot be subjective.", stat.posInUserCode.firstCodeLine)
          if placementInfo.modality.local then
            errorAndCancel("Placed statements cannot be local.", stat.posInUserCode.firstCodeLine)
          if !canceled then
            checkPlacementType(stat, bindings, placementInfo, module)

          expr

      case stat =>
        stat
    end body

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, body)
  end normalizePlacedStatements
end PlacedStatements
