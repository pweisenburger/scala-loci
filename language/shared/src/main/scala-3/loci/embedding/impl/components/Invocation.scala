package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.mutable

@experimental
trait Invocation:
  this: Component & Commons & ErrorReporter & AccessNotation & Placements & NonPlacements & Peers & AccessPath & PlacedValueSynthesis & RemoteAccessorSynthesis =>
  import quotes.reflect.*

  private def name(symbol: Symbol) =
    if symbol.isClassDef && symbol.isModuleDef then symbol.companionModule.name else symbol.name

  private def isSuperAccess(term: Term): Boolean = term match
    case term: Select => (term.name startsWith "super$") || isSuperAccess(term.qualifier)
    case term: Super => true
    case _ => false

  private def accessPath(term: Select, module: Symbol, peer: Symbol): Option[Term] =
    val path = multitierAccessPath(term, module, peer)

    if path.isEmpty && isMultitierNestedPath(term.qualifier.symbol) then
      val reference =
        if isSuperAccess(term) then
          val name = term.safeShow(term.symbol.name).replace(".this.super$", ".super.").replace("super$", "super.")
          if name.last == '$' then name.init else name
        else
          s"${name(term.symbol)} of multitier module ${name(term.qualifier.symbol)}"
      errorAndCancel(
        s"Access to value $reference not allowed from module ${fullName(module)}",
        term.posInUserCode.lastCodeLine)

    path
  end accessPath

  private def insideApplications(term: Term)(f: Term => Option[Term]): Option[Term] = term match
    case NonPlacedArgumentApplication(fun) =>
      insideApplications(fun)(f)
    case TypeApply(fun, args) =>
      insideApplications(fun)(f) map { TypeApply.copy(term)(_, args) }
    case Apply(fun, args) =>
      insideApplications(fun)(f) map { Apply.copy(term)(_, args) }
    case _ =>
      f(term)

  private def checkSelectionNotation(select: Select, selected: List[Term]) =
    val code = SourceCode(select.qualifier.pos.sourceFile)
    val index = code.forwardSkipToToken(select.qualifier.pos.end)
    if index < code.length && code(index) == '.' then
      val access = select.qualifier.pos.sourceCode filterNot { _ exists { ch => ch == '\r' || ch == '\n' } } getOrElse "<placed value>"
      val args = selected match
        case List(selected) => selected.pos.sourceCode filterNot { _ exists Character.isWhitespace } getOrElse "<...>"
        case _ => "(...)"
      report.warning(
        s"Discouraged placed value selection notation. Expected notation: `$access ${select.name} $args`",
        Position(select.qualifier.pos.sourceFile, index, index))

  private object SubjectiveLocalAccess:
    def unapply(term: Term) = term match
      case Apply(Apply(TypeApply(Select(expr @ PlacedValueReference(reference, placementInfo), names.to), _), List(remote)), _)
          if term.symbol.maybeOwner == symbols.placed =>
        Some(expr, reference, placementInfo, remote)
      case _ =>
        None

  private object Selection:
    def unapply(term: Term) = term match
      case Apply(TypeApply(select @ Select(value, names.from), List(remoteTypeTree)), VarArgs(remotes)) if term.symbol.maybeOwner == symbols.placed =>
        checkSelectionNotation(select, remotes)
        Some(value, Some(Left(remoteTypeTree.tpe, remotes)))
      case TypeApply(Select(value, names.from), List(remoteTypeTree)) if term.symbol.maybeOwner == symbols.placed =>
        Some(value, Some(Right(remoteTypeTree.tpe)))
      case _ =>
        None

  private object CallSelection:
    def unapply(term: Term) = term match
      case Apply(typeApply @ TypeApply(_, remoteTypeTree :: _), VarArgs(remotes)) if term.symbol.maybeOwner == symbols.select =>
        Some(Left(remoteTypeTree.tpe, remotes), () => s"remote(${argsNotation(remotes)})", notationCheck(typeApply, infix = false))
      case TypeApply(_, List(remoteTypeTree)) if term.symbol == symbols.remoteApply =>
        val (arg, pos) = notationPositionCheck(term.pos, infix = false, applied = true) match
          case (Some(arg), pos) if arg forall { ch => ch != '\r' && ch != '\n' } => (arg, pos)
          case (_, pos) => ("...", pos)
        Some(Right(remoteTypeTree.tpe), () => s"remote[$arg]", pos)
      case _ =>
        None

  private object Call:
    def unapply(term: Term) = term match
      case Apply(Apply(typeApply @ TypeApply(Select(selection, _), _), List(value)), _) if term.symbol.maybeOwner == symbols.call =>
        val (result, construct, pos) = selection match
          case CallSelection(selection, construct, pos) =>
            ((value, Some(selection)), () => s"${construct()} call", pos orElse notationCheck(typeApply, infix = true))
          case _ =>
            ((value, None), () => "remote call", notationCheck(typeApply, infix = true))
        pos foreach: pos =>
          report.warning(s"Discouraged remote call notation. Expected notation: `${construct()}`", pos)
        Some(result)
      case _ =>
        None

  private object PlacedAccessRetrieval:
    def unapply(term: Term) = term match
      case select @ Select(PlacedAccess(term, apply, arg, typeApplies, prefix, transmission, suffix), name) =>
        if apply.symbol.isExtensionMethod then
          Some(term, apply, arg, typeApplies, prefix, transmission, suffix, Some(select.symbol), Some(apply.symbol.name))
        else
          Some(term, apply, arg, typeApplies, prefix, transmission, suffix, Some(select.symbol), Some(select.symbol.name))
      case PlacedAccess(term, apply, arg, typeApplies, prefix, transmission, suffix) =>
        if apply.symbol.isExtensionMethod then
          Some(term, apply, arg, typeApplies, prefix, transmission, suffix, None, Some(apply.symbol.name))
        else
          Some(term, apply, arg, typeApplies, prefix, transmission, suffix, None, None)
      case _ =>
        None

  private enum SelectionMode(val maybeType: Option[TypeRepr], val instanceBased: Boolean):
    val instances: Term
    val instancesCount: Int
    case Single(tpe: TypeRepr, instances: Term, instancesCount: Int) extends SelectionMode(Some(tpe), instanceBased = true)
    case Multiple(tpe: TypeRepr, instances: Term, instancesCount: Int) extends SelectionMode(Some(tpe), instanceBased = true)
    case All(tpe: TypeRepr, instances: Term, instancesCount: Int) extends SelectionMode(Some(tpe), instanceBased = false)
    case None(instances: Term, instancesCount: Int) extends SelectionMode(Option.empty, instanceBased = false)

  private object SelectionMode:
    private def seq(elements: List[Term], tpe: TypeRepr) =
      Select.unique(Ref(symbols.seq.companionModule), names.apply)
        .appliedToType(tpe)
        .appliedTo(
          Typed(
            Repeated(elements, TypeTree.of(using tpe.asType)),
            TypeTree.of(using symbols.repeated.typeRef.appliedTo(tpe).asType)))

    private def remoteSeq(remote: TypeRepr, remotes: List[Term]) =
      seq(remotes, symbols.remote.typeRef.appliedTo(remote))

    private def emptyRemoteSeq =
      seq(List.empty, types.remoteRef)

    private def mappedRemoteRefSeq(remote: TypeRepr, remotes: Term)(owner: Symbol) =
      remotes.select(symbols.iterableMap)
        .appliedToType(types.remoteRef)
        .appliedTo(
          Lambda(
            owner,
            MethodType(List("remote"))(_ => List(symbols.remote.typeRef.appliedTo(remote)), _ => types.remoteRef),
            (_, args) =>
              Ref(symbols.remote.companionModule).select(symbols.remoteReference)
                .appliedToType(remote)
                .appliedTo(Ref(args.head.symbol))))

    def apply(selection: Option[Either[(TypeRepr, List[Term]), TypeRepr]])(owner: Symbol) =
      selection.fold(SelectionMode.None(emptyRemoteSeq, instancesCount = 0)):
        _.fold(
          (remote, remotes) => remotes match
            case List(remotes) if !(remotes.tpe =:= TypeRepr.of[Nothing]) && remotes.tpe <:< types.seq =>
              SelectionMode.Multiple(remote, mappedRemoteRefSeq(remote, remotes)(owner), instancesCount = -1)
            case _ if remotes.sizeIs == 1 =>
              SelectionMode.Single(remote, mappedRemoteRefSeq(remote, remoteSeq(remote, remotes))(owner), instancesCount = 1)
            case _ =>
              SelectionMode.Multiple(remote, mappedRemoteRefSeq(remote, remoteSeq(remote, remotes))(owner), instancesCount = remotes.size),
          remote =>
            SelectionMode.All(remote, emptyRemoteSeq, instancesCount = -1))
  end SelectionMode

  private def destructPlacedValueAccess(
      module: Symbol,
      term: Term,
      value: Term,
      localPeerType: TypeRepr,
      selectionMode: SelectionMode,
      retrieval: Option[(TypeRepr, TypeRepr, Option[String])],
      call: Boolean) =
    value match
      case PlacedValueReference(reference, placementInfo) =>
        selectionMode.maybeType foreach: remotePeerType =>
          if !(remotePeerType <:< placementInfo.peerType) then
            errorAndCancel(
              s"Selected remote peer ${remotePeerType.prettyShowFrom(module)} " +
              s"is not a subtype of the peer ${placementInfo.peerType.prettyShowFrom(module)} of the placed value",
              if call then term.posInUserCode.firstCodeLine else term.posInUserCode.lastCodeLine)

        if placementInfo.modality.local then
          errorAndCancel(
            "Local placed value cannot be accessed remotely.",
            term.posInUserCode.firstCodeLine)

        placementInfo.modality.subjectivePeerType foreach: subjective =>
          if !(localPeerType <:< subjective) then
            errorAndCancel(
              s"Remote value that is subjectively dispatched to ${subjective.prettyShowFrom(module)} peer " +
              s"cannot be accessed on ${placementInfo.peerType.prettyShowFrom(module)} peer.",
              term.posInUserCode.firstCodeLine)

        retrieval foreach: (local, remote, name) =>
          if !(local =:= localPeerType) then
            errorAndCancel(
              s"Remote access resolved the local peer as ${local.prettyShowFrom(module)} " +
              s"but the local peer is ${localPeerType.prettyShowFrom(module)}.",
              term.posInUserCode.lastCodeLine)

          val (remotePeerName, remotePeerType) =
            selectionMode.maybeType.fold("remote peer of the placed value", placementInfo.peerType) { ("selected remote peer", _) }

          if !(remote =:= remotePeerType) then
            errorAndCancel(
              s"Remote access resolved the remote peer as ${remote.prettyShowFrom(module)} " +
              s"but the $remotePeerName is ${placementInfo.peerType.prettyShowFrom(module)}.",
              term.posInUserCode.lastCodeLine)

          reference.symbol.info match
            case ByNameType(_) =>
            case MethodType(_, _, _) =>
              if !call then
                val invocation = "remote call <method>"
                val access = name.fold(s"`$invocation`") { name => s"`$invocation` or `($invocation).$name`" }
                errorAndCancel(
                  s"Remote access to placed method has to be invoked using $access.",
                  reference.posInUserCode.firstCodeLine)
            case _ =>
              if call then
                report.info(
                  "Remote access to placed value does not require `remote call` construct.",
                  reference.posInUserCode.firstCodeLine)

        def calledArguments(term: Term): (Term, List[Term]) = term match
          case Apply(fun, args) => fun.tpe.widenTermRefByName match
            case MethodType(_, types, _) =>
              val (term, initialArgs) = calledArguments(fun)
              val followingArgs =
                types lazyZip args collect:
                  case (tpe, arg) if meaningfulArgumentType(tpe) => arg
              (term, initialArgs ++ followingArgs)
            case _ =>
              (term, List.empty)
          case _ =>
            (term, List.empty)

        val (expr, arguments) = calledArguments(reference)

        if isSuperAccess(expr) then
          errorAndCancel("Remote access to super value is not allowed.", expr.posInUserCode.firstCodeLine)

        Option.when(!canceled) { (placementInfo, expr, arguments) }

      case _ =>
        errorAndCancel("Unexpected shape of placed value.", value.posInUserCode.firstCodeLine)
        None
  end destructPlacedValueAccess

  private def checkTieMultiplicities(
      module: Symbol,
      term: Term,
      local: TypeRepr,
      remote: TypeRepr,
      selectionMode: SelectionMode,
      tie: Option[TypeRepr],
      call: Boolean) =
    PeerInfo.check(local) match
      case Left(message, _) =>
        errorAndCancel(message, term.posInUserCode.firstCodeLine)

      case Right(localPeerInfo) =>
        val multiplicity = selectionMode match
          case SelectionMode.Single(_, _, _) =>
            Some(Multiplicity.Single)
          case SelectionMode.Multiple(_, _, _) =>
            Some(Multiplicity.Multiple)
          case _ =>
            localPeerInfo.ties.foldLeft(Option.empty[Multiplicity]):
              case (multiplicity, (tiedRemote, tiedMultiplicity)) =>
                if tiedRemote =:= remote && (multiplicity forall { _.ordinal > tiedMultiplicity.ordinal }) then Some(tiedMultiplicity)
                else if tiedRemote <:< remote && multiplicity.isEmpty then Some(Multiplicity.Multiple)
                else multiplicity

        tie match
          case Some(tie) =>
            def multiplicityName(tpe: TypeRepr) =
              val name = tpe.typeSymbol.name
              if selectionMode.instanceBased then name.toLowerCase else name

            val prefix = if selectionMode.instanceBased then "the selection is specified to be" else "the tie is specified as"

            val tieMismatchMessage = multiplicity match
              case Some(Multiplicity.Single) if !(tie =:= types.single) => Some(s"$prefix ${multiplicityName(types.single)}")
              case Some(Multiplicity.Optional) if !(tie =:= types.optional) => Some(s"$prefix ${multiplicityName(types.optional)}")
              case Some(Multiplicity.Multiple) if !(tie =:= types.multiple) => Some(s"$prefix ${multiplicityName(types.multiple)}")
              case None => Some("no tie is specified")
              case _ => None

            tieMismatchMessage foreach: message =>
              val prefix =
                if selectionMode.instanceBased then
                  s"Remote access resolved the selection of ${remote.prettyShowFrom(module)} peers to be"
                else
                  s"Remote access resolved the tie from ${local.prettyShowFrom(module)} peer " +
                  s"to ${remote.prettyShowFrom(module)} peer as"
              errorAndCancel(
                s"$prefix ${multiplicityName(tie)} but $message.",
                if call then term.posInUserCode.firstCodeLine else term.posInUserCode.lastCodeLine)

          case _ =>
            if multiplicity.isEmpty then
              errorAndCancel(
                s"No tie is specified from ${local.prettyShowFrom(module)} peer " +
                s"to ${remote.prettyShowFrom(module)} peer.",
                if call then term.posInUserCode.firstCodeLine else term.posInUserCode.lastCodeLine)
  end checkTieMultiplicities

  private object invocationRewriter extends SafeTreeMap(quotes):
    private val modules = mutable.Stack.empty[Symbol]
    private val peersTypes = mutable.Stack.empty[TypeRepr]
    private val placedValues = mutable.Stack.empty[Map[Symbol, TypeRepr]]

    extension [S](stack: mutable.Stack[S]) private def runStacked[T](value: Option[S])(body: => T) =
      value.fold(body): value =>
        stack.push(value)
        val result = body
        stack.pop()
        result

    def transformTermSkippingExpectedPlacedValues(term: Term)(owner: Symbol) = term match
      case term @ Select(PlacedValueReference(_, _), _) if term.symbol.owner == symbols.placed =>
        Select.copy(term)(super.transformTerm(term.qualifier)(owner), term.name)

      case term @ Apply(_, _) =>
        val fun = transformTerm(term.fun)(owner)
        val args = clearTypeApplications(term.fun).tpe match
          case MethodType(_, paramTypes, _) =>
            paramTypes lazyZip term.args map: (tpe, arg) =>
              if !(tpe =:= TypeRepr.of[Nothing]) && tpe <:< types.placedValue then
                super.transformTerm(arg)(owner)
              else
                transformTerm(arg)(owner)
          case _ =>
            transformTerms(term.args)(owner)
        Apply.copy(term)(fun, args)

      case _ =>
        super.transformTerm(term)(owner)
    end transformTermSkippingExpectedPlacedValues

    override def transformTerm(term: Term)(owner: Symbol) =
      if !canceled then
        val module = modules.head

        peersTypes.headOption.fold(super.transformTerm(term)(owner)): peerType =>
          def peerAccessPath(term: Term, necessarilyPlaced: Boolean) =
            val path = termAsSelection(term, module) flatMap { accessPath(_, module, peerType.typeSymbol) }
            if necessarilyPlaced && path.isEmpty then
              errorAndCancel("Unexpected shape of placed value.", term.posInUserCode)
            path

          def remoteAccessArguments(remote: TypeRepr, reference: Term, arguments: List[Term]) =
            if !canceled && peerAccessPath(reference, necessarilyPlaced = true).nonEmpty then
              val key =
                if (reference.symbol.flags is Flags.Synthetic) && (reference.symbol.name startsWith names.block) then
                  try reference.symbol.name.drop(names.block.length).toInt
                  catch case _: NumberFormatException => reference.symbol
                else
                  reference.symbol

              val path = termAsSelection(reference, module) match
                case Some(reference) =>
                  Some(reference.qualifier)
                case _ =>
                  errorAndCancel("Unexpected shape of placed value.", reference.posInUserCode.firstCodeLine)
                  None

              path flatMap: path =>
                synthesizeAllPlacedAccessors(path.symbol).get(key) match
                  case Some(placed) =>
                    synthesizeAllPeerSignatures(path.symbol).get(remote.typeSymbol) match
                      case Some(signature) =>
                        val args =
                          if hasSyntheticMultitierContextArgument(reference.symbol) then
                            arguments.init
                          else
                            arguments
                        Some(
                          Select.unique(This(synthesizedPlacedValues(module, peerType.typeSymbol).symbol), names.system),
                          path.select(placed),
                          path.select(signature),
                          if args.isEmpty then Literal(UnitConstant())
                          else if args.sizeIs == 1 then args.head
                          else Tuple(args map { transformTerm(_)(owner) }))
                      case _ =>
                        errorAndCancel("Unexpected remote access to value on peer without a signature.", term.posInUserCode.lastCodeLine)
                        None
                  case _ =>
                    errorAndCancel("Unexpected remote access to placed value without an accessor.", term.posInUserCode.lastCodeLine)
                    None
            else
              None
          end remoteAccessArguments

          term match
            // remote access to placed values of other peer instances using accessor syntax (possibly combined with remote procedure syntax)
            case PlacedAccessRetrieval(expr, apply, arg, typeApplies, prefix, transmission, suffix, select, name) =>
              val List(v, r, t, l, m) = transmission.tpe.widenTermRefByName.dealias.typeArgs: @unchecked

              val (value, selection, call) = arg match
                case Call(value, selection) => (value, selection, true)
                case Selection(value, selection) => (value, selection, false)
                case _ => (arg, None, false)

              val selectionMode = SelectionMode(selection)(owner)
              val access = destructPlacedValueAccess(module, term, value, peerType, selectionMode, Some(l, r, name), call)

              val result =
                access flatMap: (_, reference, arguments) =>
                  checkTieMultiplicities(module, term, l, r, selectionMode, Some(m), call)

                  remoteAccessArguments(r, reference, arguments) map: (system, placed, signature, arguments) =>
                    val result =
                      ValDef.let(owner, "instances", selectionMode.instances): instances =>
                        val arg = Ref(symbols.remoteValue).appliedToTypes(List(r, v)).appliedToNone
                        val instanceBased = Literal(BooleanConstant(selectionMode.instanceBased))
                        val request =
                          New(TypeIdent(symbols.remoteRequest)).select(symbols.remoteRequest.primaryConstructor)
                            .appliedToTypes(List(v, r, t, l, m, placed.tpe.widenTermRefByName.dealias.typeArgs.head))
                            .appliedTo(arguments, placed, signature, instances, instanceBased, system)

                        val access = PlacedAccess(
                          expr,
                          apply,
                          arg,
                          transformSubTrees(typeApplies)(owner),
                          transformTerms(prefix)(owner),
                          request,
                          transformTerms(suffix)(owner))

                        select.fold(access) { access.select(_) }
                    end result

                    val Block((valDef: ValDef) :: stats, term) = result: @unchecked
                    Block.copy(result)(ValDef.copy(valDef)(valDef.name, valDef.tpt, valDef.rhs map { _.changeOwner(valDef.symbol) }) :: stats, term)
              end result

              result getOrElse super.transformTerm(term)(owner)

            // remote access to placed values of other peer instances using remote procedure syntax (without accessor syntax)
            case Call(value, selection) =>
              val selectionMode = SelectionMode(selection)(owner)
              val access = destructPlacedValueAccess(module, term, value, peerType, selectionMode, retrieval = None, call = true)

              val result =
                access flatMap: (placementInfo, reference, arguments) =>
                  val remotePeerType = selectionMode.maybeType getOrElse placementInfo.peerType
                  checkTieMultiplicities(module, term, peerType, remotePeerType, selectionMode, tie = None, call = true)

                  remoteAccessArguments(remotePeerType, reference, arguments) map: (system, placed, signature, arguments) =>
                    val result =
                      ValDef.let(owner, "instances", selectionMode.instances): instances =>
                        val typeArgs = placed.tpe.widenTermRefByName.dealias.typeArgs
                        val requestResult = Literal(BooleanConstant(false))
                        val access =
                          system.select(symbols.invokeRemoteAccess)
                            .appliedToTypes(List(typeArgs.head, typeArgs.last))
                            .appliedTo(arguments, placed, signature, instances, requestResult)

                        if selectionMode.instanceBased then
                          selectionMode.instancesCount match
                            case -1 => If(instances.select(symbols.iterableNonEmpty), Block(List(access), Literal(UnitConstant())), Literal(UnitConstant()))
                            case 0 => Literal(UnitConstant())
                            case _ => access
                        else
                          access
                    end result

                    val Block((valDef: ValDef) :: stats, term) = result: @unchecked
                    Block.copy(result)(ValDef.copy(valDef)(valDef.name, valDef.tpt, valDef.rhs map { _.changeOwner(valDef.symbol) }) :: stats, term)
              end result

              result getOrElse super.transformTerm(term)(owner)

            // local access to subjective placed values
            case SubjectiveLocalAccess(expr, reference, placementInfo, remote) =>
              val transformedExpr = transformTerm(expr)(owner)
              val transformedRemote = transformTerm(remote)(owner)

              placementInfo.modality.subjectivePeerType.fold(transformedExpr): subjective =>
                val instance =
                  if transformedRemote.tpe =:= TypeRepr.of[Nothing] then
                    None
                  else if !(transformedRemote.tpe derivesFrom symbols.remote) then
                    Some("another")
                  else
                    val remote = transformedRemote.tpe.baseType(symbols.remote).typeArgs.head
                    if !(remote <:< subjective) then
                      Some(remote.prettyShowFrom(module))
                    else
                      None

                instance match
                  case Some(instance) =>
                    errorAndCancel(
                      s"Value that is subjectively dispatched to ${subjective.prettyShowFrom(module)} peer " +
                      s"cannot be invoked for $instance peer instance.",
                      term.posInUserCode.firstCodeLine)
                    term
                  case _ =>
                    if isStablePath(reference) then
                      Select.unique(This(synthesizedPlacedValues(module, peerType.typeSymbol).symbol), names.system)
                        .select(symbols.subjectiveValue)
                        .appliedToTypes(List(placementInfo.valueType, subjective))
                        .appliedTo(transformedExpr, transformedRemote)
                    else
                      transformedExpr.select(symbols.function1Apply).appliedTo(transformedRemote)

            // placed value access on the same peer
            case PlacedValueReference(reference, placementInfo) =>
              val expr = insideApplications(reference): term =>
                if !(peerType <:< placementInfo.peerType) then
                  val value =
                    if !(term.symbol.flags is Flags.Synthetic) && !(term.symbol.flags is Flags.Artifact) then
                      s"value ${name(term.symbol)}"
                    else
                      "value"
                  errorAndCancel(
                    s"Access to $value on ${placementInfo.peerType.prettyShowFrom(module)} peer not allowed " +
                    s"on ${peerType.prettyShowFrom(module)} peer.",
                    reference.posInUserCode.firstCodeLine)
                  None
                else
                  peerAccessPath(term, necessarilyPlaced = true)

              transformTermSkippingExpectedPlacedValues(expr getOrElse term)(owner)

            // non-placed value access in multitier modules with non-placed context argument
            case NonPlacedArgumentApplication(fun) =>
              transformTerm(fun)(owner)

            // non-placed value access in multitier modules with non-placed context function return type
            case NonPlacedValueReference(reference, _) =>
              val expr = insideApplications(reference): term =>
                peerAccessPath(term, necessarilyPlaced = false)
              transformTermSkippingExpectedPlacedValues(expr getOrElse term)(owner)

            // non-placed value access in multitier modules without non-placed context function type
            case _: Ref =>
              if PlacementInfo(term.tpe.widenTermRefByName.resultType).isEmpty then
                val multitierNestedPath = term match
                  case This(_) | Super(_, _) => false
                  case _ => term.symbol.exists && !term.symbol.isClassConstructor && isMultitierNestedPath(term.symbol.maybeOwner)
                transformTermSkippingExpectedPlacedValues(peerAccessPath(term, multitierNestedPath) getOrElse term)(owner)
              else
                transformTermSkippingExpectedPlacedValues(term)(owner)

            case _ =>
              transformTermSkippingExpectedPlacedValues(term)(owner)
      else
        term
    end transformTerm

    override def transformStatement(stat: Statement)(owner: Symbol) = stat match
      case stat: ClassDef if !canceled =>
        val symbol = stat.symbol
        val peerType =
          placedValues.headOption flatMap { _.get(symbol) } orElse:
            Option.when(!isMultitierModule(symbol)) { defn.AnyClass.typeRef }

        val definitions =
          if isMultitierModule(symbol) then
            PeerInfo.ofModule(symbol) map: peerInfo =>
              synthesizedPlacedValues(symbol, peerInfo.peerType.typeSymbol).symbol -> peerInfo.peerType
          else
            List.empty

        if !isMultitierModule(symbol) || placedValues.isEmpty then
          placedValues.runStacked(Some(definitions.toMap)):
            peersTypes.runStacked(peerType):
              modules.runStacked(Option.when(isMultitierNestedPath(symbol)) { symbol }):
                super.transformStatement(stat)(owner)
        else
          stat

      case _ if !canceled =>
        placedValues.runStacked(Some(Map.empty)):
          super.transformStatement(stat)(owner)

      case _ =>
        stat
    end transformStatement
  end invocationRewriter

  def rewireInvocations(module: ClassDef): ClassDef =
    invocationRewriter.transformSubTrees(List(module))(module.symbol.owner).head
end Invocation
