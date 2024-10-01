package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.mutable
import scala.quoted.*
import scala.util.control.NonFatal

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
          case (Some(bindings, compounds), MaybeInlined(closure @ Lambda(List(arg), body)))
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
      case binding @ ValDef(_, tpt, Some(Apply(_, VarArgs(List(expr)))))
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
          val block @ Block(List(lambda: DefDef), closure @ Closure(method, _)) =
            Lambda(binding.symbol.owner, tpe, (symbol, _) => body.changeOwner(symbol)): @unchecked
          bindings ->
            Block.copy(block)(List(lambda), Closure.copy(closure)(method, Some(placementInfo.canonicalType)))

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
      checkBindings(stat, placementConstructsBindings)

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
        errorAndCancel(s"Placed type cannot be a context function type: ${placementInfo.valueType.prettyShow}", pos)
      else if !placementInfo.canonical then
        val message = tpt match
          case Inferred() => "Placement type could not be inferred. Explicit type ascription required."
          case _ => "Invalid placement type."
        errorAndCancel(
          s"$message Expected type: ${placementInfo.showCanonicalFrom(stat.symbol.owner)}\n" +
          s"Placement types are imported by: import loci.language.*", pos)
      placementInfo.canonical

  private def statementTypeTreeInfo(stat: Statement) = stat match
    case ValDef(_, Inferred(), _) | DefDef(_, _, Inferred(), _) => (stat.posInUserCode.firstCodeLine, true)
    case ValDef(_, tpt, _) => (tpt.posInUserCode, false)
    case DefDef(_, _, tpt, _) => (tpt.posInUserCode, false)
    case _ => (stat.posInUserCode.firstCodeLine, false)

  private def checkBindings(stat: Statement, placementConstructsBindings: List[Definition]): Unit =
    val acceptableBindingsCount = stat match
      case PlacedStatement(_) | _: Term => 1
      case _ =>  0
    placementConstructsBindings.drop(acceptableBindingsCount) foreach: binding =>
      val bindingPosition = binding.posInUserCode
      val pos = if bindingPosition == Position.ofMacroExpansion then stat.posInUserCode else bindingPosition
      errorAndCancel("Illegal use of multitier construct.", pos.firstCodeLine)

  private def checkBindings(stat: Statement, placementConstructsBindings: Iterable[List[Definition]]): Unit =
    placementConstructsBindings.iterator.zipWithIndex foreach: (placementConstructsBindings, index) =>
      if index == 0 || !canceled then
        checkBindings(stat, placementConstructsBindings)

  private def checkPeerType(stat: Statement, peerType: TypeRepr, module: ClassDef, statement: String, relation: String): Unit =
    if PeerInfo(peerType).isEmpty then
      errorAndCancel(
        s"$statement must be $relation a peer type but is $relation ${peerType.prettyShowFrom(module.symbol)}.",
        stat.posInUserCode.firstCodeLine)
    if peerType.typeSymbol != defn.AnyClass && !(peerType =:= ThisType(module.symbol).select(peerType.typeSymbol)) then
      val symbol = module.symbol
      val name = if symbol.isClassDef && symbol.isModuleDef then symbol.companionModule.name else symbol.name
      errorAndCancel(
        s"$statement must be $relation a peer of module $name but is $relation peer ${peerType.prettyShowFrom(module.symbol)}.",
        stat.posInUserCode.firstCodeLine)

  private def checkPlacementInfo(definition: Statement, stat: Statement, placementInfo: PlacementInfo, module: ClassDef): Unit =
    val (statement, subjectiveStatement) = definition match
      case _ if definition != stat => ("Placement compound", "Subjective placement compound")
      case _: ValDef | _: DefDef => ("Placed definition", "Subjective placed definition")
      case _ => ("Placed statement", "Subjective placed statement")
    checkPeerType(stat, placementInfo.peerType, module, statement, "placed on")
    placementInfo.modality.subjectivePeerType foreach { checkPeerType(stat, _, module, subjectiveStatement, "subjective to") }

  private def checkPlacementBindings(stat: Statement, bindings: List[List[Definition]], placementInfo: PlacementInfo, module: ClassDef): Unit =
    val (placementConstructsBindings, hasNonSyntheticPlacedConstructBindings) = bindingsForPlacementConstructs(bindings)

    checkPlacementInfo(stat, stat, placementInfo, module)
    checkBindings(stat, placementConstructsBindings)

    val isPlacementCompound =
      bindings.iterator.flatten exists:
        _.symbol.info.typeSymbol == symbols.lowestCommonSuperType

    val (pos, inferred) = statementTypeTreeInfo(stat)

    if inferred && ((placementConstructsBindings forall { _.isEmpty }) || hasNonSyntheticPlacedConstructBindings) then
      errorAndCancel(s"Placed definitions without type ascription must be enclosed in a placed block: on[${placementInfo.peerType.prettyShowFrom(module.symbol)}]", pos)
    else if isPlacementCompound && hasNonSyntheticPlacedConstructBindings then
      errorAndCancel("Illegal use of multitier construct.", stat.posInUserCode.firstCodeLine)

    if !canceled then
      checkPlacementNotation(placementInfo, stat, bindings)
      checkPlacementCompoundNotation(stat, bindings)
  end checkPlacementBindings

  private def checkPlacementCompoundNotation(stat: Statement, bindings: List[List[Definition]]) =
    bindings.iterator.flatten foreach: binding =>
      if binding.pos.sourceFile == stat.pos.sourceFile then
        val code = SourceCode(binding.pos.sourceFile)
        var end = code.backwardSkipToToken(code.backwardSkipToken(binding.pos.start))
        while end >= 0 && (code(end) == '(' || code(end) == '{') do
          end = code.backwardSkipToToken(end - 1)

        val colon = end >= 0 && code(end) == ':'
        if colon then
          end = code.backwardSkipToToken(end - 1)
          while end >= 0 && code(end) == ')' do
            end = code.backwardSkipToToken(end - 1)

        val typeArguments = end >= 0 && code(end) == ']'
        if typeArguments then
          end = code.backwardSkipToToken(code.backwardSkipToMatchingBracket(end) - 1)

        var start = code.backwardSkipToken(end)
        if start >= 0 && (!colon || typeArguments) then
          val token = code.view.slice(start + 1, end + 1).mkString
          if token == "and" || token == "`and`" then
            start = code.backwardSkipToken(end)
            val dot = start >= 0 && code(start) == '.'
            if dot || typeArguments then
              val construct =
                if dot && colon then ".and:"
                else "(on[...] { ... }) and (on[...] { ... })"
              report.warning(
                s"Discouraged placement compound notation. Expected notation: `$construct`",
                Position(binding.pos.sourceFile, start, start))
  end checkPlacementCompoundNotation

  private def checkPlacementNotation(placementInfo: PlacementInfo, stat: Statement, bindings: List[List[Definition]]) =
    val code = SourceCode(stat.pos.sourceFile)
    val definitionStart = stat match
      case ValDef(_, tpt, _) => tpt.pos.end
      case DefDef(_, _, tpt, _) => tpt.pos.end
      case _ => stat.pos.start

    bindings.iterator.flatten foreach: binding =>
      if binding.pos.sourceFile == stat.pos.sourceFile then
        var start, end, next = 0
        var token = ""

        inline def nextToken(from: Int) =
          start = code.forwardSkipToToken(from)
          end = code.forwardSkipToken(start)
          next = code.forwardSkipToToken(end)

        inline def makeToken() =
          token = code.view.slice(start, end).mkString

        nextToken(math.max(binding.pos.start, definitionStart))
        while start < code.length && code(start) == '=' do
          nextToken(next)
        while start < code.length && (code(start) == '(' || code(start) == '{') do
          nextToken(next)
        while next < code.length && code(next) == '.' do
          nextToken(next + 1)

        makeToken()
        if token == "and" || token == "`and`" then
          nextToken(next)
          while start < code.length && (code(start) == '(' || code(start) == '{' || code(start) == ':') do
            nextToken(next)
          makeToken()

        if (token == "on" || token == "`on`") && next < code.length && code(next) == '[' then
          start = next
          end = code.forwardSkipToMatchingBracket(next) + 1
          next = code.forwardSkipToToken(end)
          val dot = next < code.length && code(next) == '.'

          makeToken()
          val peer = if token exists { ch => ch == '\r' || ch == '\n' } then "[...]" else token

          val pos =
            if dot then
              val pos = Position(stat.pos.sourceFile, next, next)
              nextToken(next + 1)
              makeToken()
              pos
            else
              nextToken(next)
              makeToken()
              Position(stat.pos.sourceFile, start, end)

          val local = token == "local" || token == "`local`"
          val sbj = token == "sbj" || token == "`sbj`"
          val apply = token == "apply" || token == "`apply`"

          val construct =
            if dot && local then Some(" local")
            else if dot && sbj then Some(" sbj")
            else if apply then Some("")
            else None

          construct foreach: construct =>
            val block = if next < code.length && code(next) == ':' then ":" else " { ... }"
            report.warning(s"Discouraged placement notation. Expected notation: `on$peer$construct$block`", pos)

          if local && !placementInfo.modality.local then
            errorAndCancel("Placed expression is local but placement type is not.", Position(stat.pos.sourceFile, start, end))
          if sbj && !placementInfo.modality.subjective then
            errorAndCancel("Placed expression is subjective but placement type is not.", Position(stat.pos.sourceFile, start, end))
  end checkPlacementNotation

  private object placementTypesEraser extends PlacementFromPlacedValueTypeEraser

  private def checkPlacedBodies(stat: Statement, expr: Term, placementInfo: PlacementInfo, module: ClassDef): Unit =
    def last(term: Term): Term = term match
      case Block(_, expr) => last(expr)
      case Inlined(_, _, body) => last(body)
      case _ => term

    val tpes = placementInfo.modality match
      case Modality.Subjective(peerType) =>
        List(
          symbols.function1.typeRef.appliedTo(List(symbols.remote.typeRef.appliedTo(peerType), placementInfo.valueType)),
          symbols.subjective.typeRef.appliedTo(List(peerType, placementInfo.valueType)))
      case _ =>
        List(placementInfo.valueType)
    val unit = tpes.head =:= TypeRepr.of[Unit]
    val peer = placementInfo.peerType.typeSymbol
    val bodies = extractPlacementBodies(expr)

    if !unit then
      bodies foreach: (expr, _) =>
        val exprType = placementTypesEraser.transform(expr.tpe)
        if tpes forall { tpe => !(exprType <:< tpe) } then
          val term = last(expr)
          tryReportTypeMismatch(term, tpes.head)
          errorAndCancel(
            s"Found:    ${exprType.widenTermRefByName.prettyShow}\n" +
            s"Required: ${tpes.head.widenTermRefByName.prettyShow}",
            term.pos)

    if !canceled then
      val peers = mutable.Set.empty[Symbol]
      bodies foreach: (expr, tpe) =>
        tpe foreach: tpe =>
          PlacementInfo(tpe) foreach: bodyPlacementInfo =>
            checkPlacementInfo(stat, expr, bodyPlacementInfo, module)
            if !canceled then
              val bodyPeerType = bodyPlacementInfo.peerType
              val bodyPeer = bodyPeerType.typeSymbol
              if !(bodyPeerType <:< placementInfo.peerType) then
                errorAndCancel(s"Peer type ${bodyPeer.name} is not a subtype of placement compound peer type ${peer.name}.", expr.posInUserCode.firstCodeLine)
              if peers contains bodyPeer then
                errorAndCancel(s"Peer type ${bodyPeer.name} appears multiple times in placement compound.", expr.posInUserCode.firstCodeLine)
              peers += bodyPeer

      if !canceled && !unit && !(peers contains placementInfo.peerType.typeSymbol) then
        errorAndCancel(s"Placement compound does not cover common super peer type ${peer.name}. The common super peer can only be left out if the placed value has type Unit.", stat.posInUserCode.firstCodeLine)
    end if
  end checkPlacedBodies

  private def tryReportTypeMismatch(tree: Tree, expected: TypeRepr) =
    try
      val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
      val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
      val typeClass = Class.forName("dotty.tools.dotc.core.Types$Type")
      val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
      val errorReportingClass = Class.forName("dotty.tools.dotc.typer.ErrorReporting")
      val errorsClass = Class.forName("dotty.tools.dotc.typer.ErrorReporting$Errors")

      val ctx = quotesImplClass.getMethod("ctx")
      val err = errorReportingClass.getMethod("err", contextClass)

      val (typeMismatch, defaultClass) =
        try
          val addendaClass = Class.forName("dotty.tools.dotc.typer.ErrorReporting$Addenda")
          val nothingToAddClass = Class.forName("dotty.tools.dotc.typer.ErrorReporting$NothingToAdd")
          val typeMismatch = errorsClass.getMethod("typeMismatch", treeClass, typeClass, addendaClass)
          (typeMismatch, nothingToAddClass)
        catch
          case NonFatal(_) =>
            val searchFailureTypeClass = Class.forName("dotty.tools.dotc.typer.Implicits$SearchFailureType")
            val noMatchingImplicitsClass = Class.forName("dotty.tools.dotc.typer.Implicits$NoMatchingImplicits$")
            val typeMismatch = errorsClass.getMethod("typeMismatch", treeClass, typeClass, searchFailureTypeClass)
            (typeMismatch, noMatchingImplicitsClass)

      val context = ctx.invoke(quotes)
      val default = defaultClass.getField("MODULE$").get(null)

      typeMismatch.invoke(err.invoke(null, context), tree, expected, default)
    catch
      case NonFatal(_) =>
  end tryReportTypeMismatch

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
    module.body foreach:
      case stat @ TypeDef(_, _) if stat.symbol.hasAnnotation(symbols.peer) =>
        PeerInfo.check(stat, shallow = true).left foreach errorAndCancel
      case _ =>

    if canceled then
      disableErrorAndCancel()

    val body = module.body map:
      case stat @ TypeDef(_, _) if stat.symbol.hasAnnotation(symbols.peer) =>
        PeerInfo.check(stat).left foreach errorAndCancel
        stat

      case stat @ ValDef(name, tpt, rhs) =>
        SingletonTypeChecker(stat).transform(tpt.tpe)
        placementType(stat, tpt).fold(cleanSpuriousPlacementSyntax(stat)): placementInfo =>
          val (bindings, expr) = cleanPlacementSyntax(placementInfo, rhs)(stat.symbol)
          checkPlacementBindings(stat, bindings, placementInfo, module)
          expr foreach { checkPlacedBodies(stat, _, placementInfo, module) }
          ValDef.copy(stat)(name, tpt, expr)

      case stat @ DefDef(name, paramss, tpt, rhs) =>
        SingletonTypeChecker(stat).transform(tpt.tpe)
        placementType(stat, tpt).fold(cleanSpuriousPlacementSyntax(stat)): placementInfo =>
          val (bindings, expr) = cleanPlacementSyntax(placementInfo, rhs)(stat.symbol)
          checkPlacementBindings(stat, bindings, placementInfo, module)
          expr foreach { checkPlacedBodies(stat, _, placementInfo, module) }
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
          checkBindings(stat, placementConstructsBindings)

          if bindings.isEmpty || hasNonSyntheticPlacedConstructBindings then
            errorAndCancel(s"Placed statements must be enclosed in a placed block: on[${placementInfo.peerType.prettyShowFrom(module.symbol)}]", stat.posInUserCode.firstCodeLine)
          else if bindings.sizeIs > 1 then
            val compound = extractPlacementBodies(expr) match
              case (_, tpe1) :: (_, tpe2) :: _ =>
                tpe1.fold(""): tpe1 =>
                  tpe2.fold(""): tpe2 =>
                    PlacementInfo(tpe1).fold(""): placementInfo1 =>
                      PlacementInfo(tpe2).fold(""): placementInfo2 =>
                        s": (on[${placementInfo1.peerType.typeSymbol.name}] <...>) and (on[${placementInfo2.peerType.typeSymbol.name}] <...>)"
              case _ => ""
            errorAndCancel(s"Placed statements cannot be compound placed expressions$compound. Consider splitting them into separate statements.", stat.posInUserCode.firstCodeLine)

          if placementInfo.modality.subjective then
            errorAndCancel("Placed statements cannot be subjective.", stat.posInUserCode.firstCodeLine)
          if placementInfo.modality.local then
            errorAndCancel("Placed statements cannot be local.", stat.posInUserCode.firstCodeLine)
          if !canceled then
            checkPlacementBindings(stat, bindings, placementInfo, module)

          expr

      case stat =>
        stat
    end body

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, body)
  end normalizePlacedStatements
end PlacedStatements
