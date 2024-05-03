package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.mutable

@experimental
trait Invocation:
  this: Component & Commons & ErrorReporter & Placements & Peers & AccessPath & PlacedValueSynthesis & RemoteAccessorSynthesis =>
  import quotes.reflect.*

  private def accessPath(term: Select, module: Symbol, peer: Symbol): Option[Term] =
    val path = multitierAccessPath(term, module, peer)
    if path.isEmpty && isMultitierNestedPath(term.qualifier.symbol) then
      errorAndCancel(
        s"Access to multitier value ${term.symbol.name} not allowed from module ${fullName(module)}",
        term.posInUserCode.endPosition)
    path

  private def insideApplications(term: Term)(f: Term => Option[Term]): Option[Term] = term match
    case TypeApply(fun, args) =>
      insideApplications(fun)(f) map { TypeApply.copy(term)(_, args) }
    case Apply(fun, args) =>
      insideApplications(fun)(f) map { Apply.copy(term)(_, args) }
    case _ =>
      f(term)

  private object Selection:
    def unapply(term: Term) = term match
      case Apply(TypeApply(Select(value, names.from), List(remoteTypeTree)), remotes) if term.symbol.owner == symbols.placed =>
        Some(value, Some(Left(remoteTypeTree.tpe, remotes)))
      case TypeApply(Select(value, names.from), List(remoteTypeTree)) if term.symbol.owner == symbols.placed =>
        Some(value, Some(Right(remoteTypeTree.tpe)))
      case _ =>
        None

  private object CallSelection:
    def unapply(term: Term) = term match
      case Apply(TypeApply(_, remoteTypeTree :: _), remotes) if term.symbol.maybeOwner == symbols.select =>
        Some(Left(remoteTypeTree.tpe, remotes))
      case TypeApply(_, List(remoteTypeTree)) if term.symbol == symbols.remoteApply =>
        Some(Right(remoteTypeTree.tpe))
      case _ =>
        None

  private object Call:
    def unapply(term: Term) = term match
      case Apply(Apply(TypeApply(Select(selection, _), _), List(value)), _) if term.symbol.maybeOwner == symbols.call =>
        selection match
          case CallSelection(selection) => Some(value, Some(selection))
          case _ => Some(value, None)
      case _ =>
        None

  private object PlacedAccessRetrieval:
    def unapply(term: Term) = term match
      case select @ Select(PlacedAccess(term, arg, typeApplies, apply, prefix, transmission, suffix), name) =>
        if term.symbol.isExtensionMethod then
          Some(term, arg, typeApplies, apply, prefix, transmission, suffix, Some(select.symbol), Some(term.symbol.name))
        else
          Some(term, arg, typeApplies, apply, prefix, transmission, suffix, Some(select.symbol), Some(select.symbol.name))
      case PlacedAccess(term, arg, typeApplies, apply, prefix, transmission, suffix) =>
        if term.symbol.isExtensionMethod then
          Some(term, arg, typeApplies, apply, prefix, transmission, suffix, None, Some(term.symbol.name))
        else
          Some(term, arg, typeApplies, apply, prefix, transmission, suffix, None, None)
      case _ =>
        None

  def rewireInvocations(module: ClassDef): ClassDef =
    object invocationRewriter extends SafeTreeMap(quotes):
      private val modules = mutable.Stack.empty[Symbol]
      private val peersTypes = mutable.Stack.empty[TypeRepr]
      private val placedValues = mutable.Stack.empty[Map[Symbol, TypeRepr]]

      extension [S](stack: mutable.Stack[S]) private def runStacked[T](value: Option[S])(body: => T) =
        value.fold(body): value =>
          stack.push(value)
          val result = body
          stack.pop()
          result

      override def transformTerm(term: Term)(owner: Symbol) =
        if !canceled then
          val module = modules.head

          peersTypes.headOption.fold(super.transformTerm(term)(owner)): peerType =>
            def peerAccessPath(term: Term, necessarilyPlaced: Boolean) =
              val path = termAsSelection(term, module) flatMap { accessPath(_, module, peerType.typeSymbol) }
              if necessarilyPlaced && path.isEmpty then
                errorAndCancel("Unexpected shape of placed value", term.posInUserCode.endPosition)
              path

            term match
              // remote access to placed values of other peer instances
              case PlacedAccessRetrieval(expr, arg, typeApplies, apply, prefix, transmission, suffix, select, name) =>
                val List(v, r, t, l, m) = transmission.tpe.widenTermRefByName.dealias.typeArgs: @unchecked

                val (value, selection, call) = arg match
                  case Call(value, selection) => (value, selection, true)
                  case Selection(value, selection) => (value, selection, false)
                  case _ => (arg, None, false)

                def seq(elements: List[Term], tpe: TypeRepr) =
                  Select.unique(Ref(symbols.seq.companionModule), names.apply)
                    .appliedToType(tpe)
                    .appliedTo(
                      Typed(
                        Repeated(elements, TypeTree.of(using tpe.asType)),
                        TypeTree.of(using symbols.repeated.typeRef.appliedTo(tpe).asType)))

                def remoteSeq(remotes: List[Term]) =
                  seq(remotes, symbols.remote.typeRef.appliedTo(r))

                def emptyRemoteSeq =
                  seq(List.empty, types.remoteRef)

                def mappedRemoteRefSeq(remotes: Term) =
                  remotes.select(symbols.iterableMap)
                    .appliedToType(types.remoteRef)
                    .appliedTo(
                      Lambda(
                        owner,
                        MethodType(List("remote"))(_ => List(symbols.remote.typeRef.appliedTo(r)), _ => types.remoteRef),
                        (_, args) =>
                          Ref(symbols.remote.companionModule).select(symbols.remoteReference)
                            .appliedToType(r)
                            .appliedTo(Ref(args.head.symbol))))

                enum SelectionMode(val maybeType: Option[TypeRepr], val instanceBased: Boolean):
                  val instances: Term
                  case Single(tpe: TypeRepr, instances: Term) extends SelectionMode(Some(tpe), instanceBased = true)
                  case Multiple(tpe: TypeRepr, instances: Term) extends SelectionMode(Some(tpe), instanceBased = true)
                  case All(tpe: TypeRepr, instances: Term) extends SelectionMode(Some(tpe), instanceBased = false)
                  case None(instances: Term) extends SelectionMode(Option.empty, instanceBased = false)

                val selectionMode =
                  selection.fold(SelectionMode.None(emptyRemoteSeq)):
                    _.fold(
                      (remote, remotes) => remotes match
                        case List(remotes) if !(remotes.tpe =:= TypeRepr.of[Nothing]) && remotes.tpe <:< types.seq =>
                          SelectionMode.Multiple(remote, mappedRemoteRefSeq(remotes))
                        case _ if remotes.sizeIs == 1 =>
                          SelectionMode.Single(remote, mappedRemoteRefSeq(remoteSeq(remotes)))
                        case _ =>
                          SelectionMode.Multiple(remote, mappedRemoteRefSeq(remoteSeq(remotes))),
                      remote =>
                        SelectionMode.All(remote, emptyRemoteSeq))

                val reference = value match
                  case PlacedValueReference(reference, placementInfo) =>
                    selectionMode.maybeType foreach: remotePeerType =>
                      if !(remotePeerType <:< placementInfo.peerType) then
                        errorAndCancel(
                          s"Selected remote peer ${remotePeerType.safeShow(Printer.SafeTypeReprShortCode)} " +
                          s"is not a subtype of the peer ${placementInfo.peerType.safeShow(Printer.SafeTypeReprShortCode)} of the placed value",
                          if call then term.posInUserCode.startPosition else term.posInUserCode.endPosition)

                    if !(l =:= peerType) then
                      errorAndCancel(
                        s"Remote access resolved the local peer as ${l.safeShow(Printer.SafeTypeReprShortCode)} " +
                        s"but the local peer is ${peerType.safeShow(Printer.SafeTypeReprShortCode)}",
                        term.posInUserCode.endPosition)

                    val (remotePeerName, remotePeerType) =
                      selectionMode.maybeType.fold("remote peer of the placed value", placementInfo.peerType) { ("selected remote peer", _) }

                    if !(r =:= remotePeerType) then
                      errorAndCancel(
                        s"Remote access resolved the remote peer as ${r.safeShow(Printer.SafeTypeReprShortCode)} " +
                        s"but the $remotePeerName is ${placementInfo.peerType.safeShow(Printer.SafeTypeReprShortCode)}",
                        term.posInUserCode.endPosition)

                    reference.symbol.info match
                      case MethodType(_, _, _) =>
                        if !call then
                          val invocation = "remote call <method>"
                          val access = name.fold(s"`$invocation`") { name => s"`$invocation` or `($invocation).$name`" }
                          errorAndCancel(
                            s"Remote access to placed method has to be invoked using $access.",
                            reference.posInUserCode.startPosition)
                      case ByNameType(_) =>
                      case _ =>
                        if call then
                          report.info(
                            s"Remote access to placed value does not require `remote call` construct.",
                            reference.posInUserCode.startPosition)

                    def calledArguments(term: Term): (Term, List[Term]) = term match
                      case Apply(fun, args) => fun.tpe.widenTermRefByName match
                        case MethodType(_, types, _) =>
                          val (term, initialArgs) = calledArguments(fun)
                          val followingArgs =
                            types zip args collect:
                              case (tpe, arg) if meaningfulArgumentType(tpe) => arg
                          (term, initialArgs ++ followingArgs)
                        case _ =>
                          (term, List.empty)
                      case _ =>
                        (term, List.empty)

                    Option.when(!canceled) { calledArguments(reference) }

                  case _ =>
                    errorAndCancel("Unexpected shape of placed value", value.posInUserCode.startPosition)
                    None
                end reference

                if !canceled then
                  PeerInfo.check(peerType) match
                    case Left(message, _) =>
                      errorAndCancel(message, term.posInUserCode.startPosition)

                    case Right(localPeerInfo) =>
                      val multiplicity = selectionMode match
                        case SelectionMode.Single(_, _) =>
                          Some(Multiplicity.Single)
                        case SelectionMode.Multiple(_, _) =>
                          Some(Multiplicity.Multiple)
                        case _ =>
                          localPeerInfo.ties.foldLeft(Option.empty[Multiplicity]):
                            case (multiplicity, (remote, m)) =>
                              if remote =:= r && (multiplicity forall { _.ordinal > m.ordinal }) then Some(m)
                              else if remote <:< r && multiplicity.isEmpty then Some(Multiplicity.Multiple)
                              else multiplicity

                      def multiplicityName(tpe: TypeRepr) =
                        val name = tpe.typeSymbol.name
                        if selectionMode.instanceBased then name.toLowerCase else name

                      val prefix = if selectionMode.instanceBased then "the selection is specified to be" else "the tie is specified as"

                      val tieMismatchMessage = multiplicity match
                        case Some(Multiplicity.Single) if !(m =:= types.single) => Some(s"$prefix ${multiplicityName(types.single)}")
                        case Some(Multiplicity.Optional) if !(m =:= types.optional) => Some(s"$prefix ${multiplicityName(types.optional)}")
                        case Some(Multiplicity.Multiple) if !(m =:= types.multiple) => Some(s"$prefix ${multiplicityName(types.multiple)}")
                        case None => Some("no tie is specified")
                        case _ => None

                      tieMismatchMessage foreach: message =>
                        val prefix =
                          if selectionMode.instanceBased then
                            s"Remote access resolved the selection of ${r.safeShow(Printer.SafeTypeReprShortCode)} peers to be"
                          else
                            s"Remote access resolved the tie from ${l.safeShow(Printer.SafeTypeReprShortCode)} peer " +
                            s"to ${r.safeShow(Printer.SafeTypeReprShortCode)} peer as"
                        errorAndCancel(s"$prefix ${multiplicityName(m)} but $message.", term.posInUserCode.endPosition)
                end if

                val result =
                  reference flatMap: (reference, arguments) =>
                    if peerAccessPath(reference, necessarilyPlaced = true).nonEmpty then
                      synthesizeAllPlacedAccessors(module).get(reference.symbol) match
                        case Some(placed) =>
                          synthesizeAllPeerSignatures(module).get(peerType.typeSymbol) match
                            case Some(signature) =>
                              val arg = insideApplications(reference): _ =>
                                Some(Ref(symbols.remoteValue).appliedToTypes(List(r, v)).appliedToNone)

                              val argument =
                                if arguments.isEmpty then Literal(UnitConstant())
                                else if arguments.sizeIs == 1 then arguments.head
                                else Tuple(arguments)

                              val placedRef = This(module).select(placed)
                              val signatureRef = This(module).select(signature)
                              val systemRef = Select.unique(This(synthesizedPlacedValues(module, peerType.typeSymbol).symbol), names.system)

                              val request =
                                New(TypeIdent(symbols.remoteRequest)).select(symbols.remoteRequest.primaryConstructor)
                                  .appliedToTypes(List(v, r, t, l, m, placedRef.tpe.widenTermRefByName.dealias.typeArgs.head))
                                  .appliedTo(
                                    argument,
                                    placedRef,
                                    signatureRef,
                                    selectionMode.instances,
                                    Literal(BooleanConstant(selectionMode.instanceBased)),
                                    systemRef)

                              val access = PlacedAccess(
                                transformSubTrees(List(expr))(owner).head,
                                arg.get,
                                transformSubTrees(typeApplies)(owner),
                                apply,
                                transformTerms(prefix)(owner),
                                request,
                                transformTerms(suffix)(owner))

                              Some(select.fold(access) { access.select(_) })
                            case _ =>
                              errorAndCancel("Unexpected remote access to value on peer without a signature.", term.posInUserCode.endPosition)
                              None
                        case _ =>
                          errorAndCancel("Unexpected remote access to placed value without an accessor.", term.posInUserCode.endPosition)
                          None
                    else
                      None

                result getOrElse super.transformTerm(term)(owner)

              case term @ Apply(_, _) =>
                val args = clearTypeApplications(term.fun).tpe match
                  case MethodType(_, paramTypes, _) =>
                    paramTypes zip term.args map: (tpe, arg) =>
                      if !(tpe =:= TypeRepr.of[Nothing]) && tpe <:< types.placedValue then
                        super.transformTerm(arg)(owner)
                      else
                        transformTerm(arg)(owner)
                  case _ =>
                    transformTerms(term.args)(owner)

                val fun = if canceled then term.fun else transformTerm(term.fun)(owner)

                Apply.copy(term)(fun, args)

              // placed values on the same peer
              case PlacedValueReference(reference, placementInfo) =>
                val expr = insideApplications(reference): term =>
                  if !(peerType <:< placementInfo.peerType) then
                    errorAndCancel(
                      s"Access to value on peer ${placementInfo.peerType.safeShow(Printer.SafeTypeReprShortCode)} not allowed " +
                      s"from peer ${peerType.safeShow(Printer.SafeTypeReprShortCode)}",
                      reference.posInUserCode.startPosition)
                    None
                  else
                    peerAccessPath(term, necessarilyPlaced = true)

                super.transformTerm(expr getOrElse term)(owner)

              // non-placed values in multitier modules
              case _ =>
                if PlacementInfo(term.tpe.widenTermRefByName.resultType).isEmpty then
                  super.transformTerm(peerAccessPath(term, necessarilyPlaced = false) getOrElse term)(owner)
                else
                  super.transformTerm(term)(owner)
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

    invocationRewriter.transformStatement(module)(module.symbol.owner) match
      case module: ClassDef @unchecked => module
  end rewireInvocations
end Invocation
