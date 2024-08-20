package loci
package embedding
package impl
package components

import runtime.Peer
import transmitter.RemoteAccessException
import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.collection.immutable.SeqMap

@experimental
trait Dispatch:
  this: Component & Commons & ErrorReporter & Placements & AccessPath & PlacedValueSynthesis & RemoteAccessorSynthesis =>
  import quotes.reflect.*

  private def position(symbol: Symbol) =
    (symbol.moduleClass orElse symbol).pos

  private enum Arguments[Result](val take: (Term => Term) => Option[Result], val ignore: Term => Result):
    case Populated extends Arguments(Some(_), Function.const(_))
    case Void extends Arguments(Function.const(None), identity)

  private def argumentApplication[Result](
      value: Term,
      arguments: Arguments[Result],
      argumentsType: TypeRepr,
      pos: Position): Option[Result] =
    val (untupledArgumentTypes, argumentTupled) = argumentsType match
      case Tuple(args) => (args, true)
      case arg if !meaningfulArgumentType(arg) => (List.empty, false)
      case arg => (List(arg), false)

    val argumentTupleClass = untupledArgumentTypes.sizeIs < 23

    def argumentApplication(tpe: TypeRepr, argumentTypes: List[TypeRepr], index: Int): Option[List[List[Result]]] = tpe match
      case MethodType(_, paramTypes, resType) =>
        val (args, nextArgumentTypes, nextIndex) =
          paramTypes.foldLeft[(Option[List[Result]], List[TypeRepr], Int)](Some(List.empty), argumentTypes, index):
            case ((args, argumentTypes, index), paramType) =>
              args.fold(None, argumentTypes, index): args =>
                val types =
                  if meaningfulArgumentType(paramType) then
                    if argumentTypes.isEmpty then None
                    else if argumentTypes.head <:< paramType then Some(argumentTypes, false)
                    else if (argumentTypes eq untupledArgumentTypes) && argumentsType <:< paramType then Some(List(argumentsType), true)
                    else None
                  else
                    Some(argumentTypes, false)

                types.fold(None, argumentTypes, index): (types, tupleExpected) =>
                  if paramType =:= TypeRepr.of[Unit] then
                    (Some(arguments.ignore(Literal(UnitConstant())) :: args), types, index)
                  else if paramType =:= TypeRepr.of[Null] then
                    (Some(arguments.ignore(Literal(NullConstant())) :: args), types, index)
                  else if paramType =:= TypeRepr.of[Nothing] then
                    (Some(arguments.ignore('{ throw new RemoteAccessException("Unexpected value of bottom type") }.asTerm) :: args), types, index)
                  else if types.nonEmpty && argumentTupled && !tupleExpected && argumentTupleClass then
                    (arguments.take(Select.unique(_, s"_${index + 1}")) map { _ :: args }, types.tail, index + 1)
                  else if types.nonEmpty && argumentTupled && !tupleExpected then
                    (arguments.take(Select.unique(_, names.apply).appliedToType(argumentsType).appliedTo(Literal(IntConstant(index)))) map { _ :: args }, types.tail, index + 1)
                  else if types.nonEmpty then
                    (arguments.take(identity) map { _ :: args }, types.tail, index + 1)
                  else
                    (None, argumentTypes, index)
        end val

        args flatMap: args =>
          argumentApplication(resType, nextArgumentTypes, nextIndex) map { args.reverse :: _ }

      case PolyType(_, _, _) =>
        errorAndCancel("Unexpected shape of placed value.", pos)
        None

      case _ =>
        Option.when(argumentTypes.isEmpty) { List.empty }
    end argumentApplication

    val application = argumentApplication(value.tpe.widenTermRefByName, untupledArgumentTypes, 0)

    if application.isEmpty && !canceled then
      errorAndCancel("Unexpected type of remote accessor.", pos)

    application flatMap: args =>
      arguments match
        case Arguments.Populated => arguments.take(arguments => value.appliedToArgss(args map { _ map { _(arguments) } }))
        case Arguments.Void => Some(arguments.ignore(value.appliedToArgss(args)))
  end argumentApplication

  private def argumentApplicationWithSubjectivity[Result](
      module: Symbol,
      owner: Symbol,
      value: Term,
      tpe: TypeRepr,
      arguments: Arguments[Result],
      argumentsType: TypeRepr,
      pos: Position): Option[Term => Result] =
    def argumentApplicationWithSubjectivityForTerm(reference: Term, application: Term) =
      PlacementInfo(tpe).fold(application): placementInfo =>
        placementInfo.modality.subjectivePeerType.fold(application): subjective =>
          val (signature, _) = synthesizePeerSignature(module, subjective.typeSymbol)

          val condition = reference.select(symbols.valueReferenceRemote).select(symbols.remoteReferenceSignature).select(symbols.peerSignatureCompare)
            .appliedToType(types.peerSignature)
            .appliedTo(This(module).select(signature))
            .appliedTo(partiallyOrderedPeerSignatureConforms)

          val access =
            if isStablePath(value) then
              Select.unique(This(owner), names.system)
                .select(symbols.subjectiveValue)
                .appliedToTypes(List(placementInfo.valueType, subjective))
                .appliedTo(application, reference.select(symbols.valueReferenceRemote))
            else
              application.select(symbols.function1Apply).appliedTo(reference.select(symbols.valueReferenceRemote))

          If(condition, access, '{ throw new RemoteAccessException(RemoteAccessException.IllegalSubjectiveAccess) }.asTerm)
    end argumentApplicationWithSubjectivityForTerm

    def argumentApplicationWithSubjectivityForArguments(reference: Term, application: Term => Term)(arguments: Term) =
      argumentApplicationWithSubjectivityForTerm(reference, application(arguments))

    argumentApplication(value, arguments, argumentsType, pos) map: application =>
      arguments match
        case Arguments.Populated => argumentApplicationWithSubjectivityForArguments(_, application)
        case Arguments.Void => argumentApplicationWithSubjectivityForTerm(_, application)
  end argumentApplicationWithSubjectivity

  private def nestedMultitierModules(module: Symbol, pos: Position) =
    def nestedMultitierModules(path: Term, dispatching: SeqMap[String, Term]): SeqMap[String, Term] =
      path.symbol.declarations.foldLeft(dispatching): (dispatching, decl) =>
        if decl.isTerm && isMultitierModule(decl) then
          dispatching.get(decl.name) match
            case Some(existing) =>
              val prefix = s"${This(module).safeShow}."
              val other = path.select(decl)
              val message =
                s"Multitier modules nested in ${fullName(module)} with the same name are not allowed: " +
                s"${existing.safeShow(existing.symbol.name).stripPrefix(prefix)} and " +
                s"${other.safeShow(other.symbol.name).stripPrefix(prefix)}"

              val positions = position(existing.symbol) flatMap { existing => position(decl) map { (existing, _) } }
              positions match
                case Some(existing, other) if existing != other =>
                  errorAndCancel(message, existing)
                  errorAndCancel(message, other)
                case _ =>
                  errorAndCancel(message, pos)

              dispatching

            case _ =>
              dispatching + (decl.name -> path.select(decl))

        else if decl.isTerm && decl.isModuleDef then
          nestedMultitierModules(path.select(decl), dispatching)

        else
          dispatching
    end nestedMultitierModules

    nestedMultitierModules(This(module), SeqMap.empty)
  end nestedMultitierModules

  private val partiallyOrderedPeerSignatureConforms = '{ summon[Peer.Signature => math.PartiallyOrdered[Peer.Signature]] }.asTerm match
    case term @ Inlined(call, List(), Apply(_, List(conforms))) => Inlined.copy(term)(call, List(), conforms)
    case term @ Inlined(call, List(), conforms) => Inlined.copy(term)(call, List(), conforms)
    case Apply(_, List(conforms)) => conforms
    case conforms => conforms

  private val tryMessageBufferRefl = '{ summon[util.Try[MessageBuffer] <:< util.Try[MessageBuffer]] }.asTerm match
    case term @ Inlined(call, List(), Apply(_, List(refl))) => Inlined.copy(term)(call, List(), refl)
    case term @ Inlined(call, List(), refl) => Inlined.copy(term)(call, List(), refl)
    case Apply(_, List(refl)) => refl
    case refl => refl

  def generateDispatching(module: ClassDef): ClassDef =
    extension (self: Map[Symbol, List[(Symbol, Term, Term) => CaseDef]])
      inline def prepend(symbol: Symbol)(term: (Symbol, Term, Term) => CaseDef) =
        self + (symbol -> (term :: self.getOrElse(symbol, List.empty)))

    val valueDispatchings =
      synthesizeAccessors(module.symbol).placed.foldRight(Map.empty[Symbol, List[(Symbol, Term, Term) => CaseDef]]):
        case ((key, (placed, _)), dispatching) =>
          val symbol = key match
            case index: Int => module.symbol.methodMember(s"${names.block}$index").head
            case symbol: Symbol @unchecked => symbol

          synthesizedDefinitions(symbol).fold(dispatching): definition =>
            definition.impls.foldRight(dispatching): (impl, dispatching) =>
              val value = This(impl.owner).select(definition.binding)
              val placedValue = This(module.symbol).select(placed)
              val argumentsType = placedValue.tpe.widenTermRefByName.typeArgs.head
              val placedType = symbol.info.widenTermRefByName.resultType
              val pos = if symbol.flags is Flags.Synthetic then module.pos.firstCodeLine else symbol.pos getOrElse module.pos.firstCodeLine

              val meaningfulArgument = meaningfulArgumentType(argumentsType)

              def result(value: Term, reference: Term) =
                placedValue.select(symbols.placedValueResult).select(symbols.marshal).appliedTo(value, reference)

              def argumentApplication[Result](arguments: Arguments[Result]) =
                argumentApplicationWithSubjectivity(module.symbol, impl.owner, value, placedType, arguments, argumentsType, pos)

              val dispatch =
                if meaningfulArgument then
                  argumentApplication(Arguments.Populated) map: argumentApplication =>
                    (owner: Symbol, request: Term, reference: Term) =>
                      placedValue.select(symbols.placedValueArguments).select(symbols.unmarshal).appliedTo(request, reference)
                        .select(symbols.tryMap)
                        .appliedToType(types.messageBuffer)
                        .appliedTo(
                          Lambda(
                            owner,
                            MethodType(List("arguments"))(_ => List(argumentsType), _ => types.messageBuffer),
                            (_, args) => result(argumentApplication(reference)(Ref(args.head.symbol)), reference)))
                else
                  argumentApplication(Arguments.Void) map: argumentApplication =>
                    (owner: Symbol, request: Term, reference: Term) =>
                      result(argumentApplication(reference), reference)

              dispatch.fold(dispatching): dispatch =>
                dispatching.prepend(impl.owner): (owner, request, reference) =>
                  val tpe =
                    if meaningfulArgument then
                      symbols.`try`.typeRef.appliedTo(types.messageBuffer)
                    else
                      types.messageBuffer

                  val tryDispatch =
                    Select.unique(Ref(symbols.`try`.companionModule), names.apply).appliedToType(tpe).appliedTo(dispatch(owner, request, reference))

                  val tryDispatchFlattened =
                    if meaningfulArgument then
                      tryDispatch.select(symbols.tryFlatten).appliedToType(types.messageBuffer).appliedTo(tryMessageBufferRefl)
                    else
                      tryDispatch

                  CaseDef(placedValue.select(symbols.placedValueSignature).select(symbols.valueSignatureName), guard = None, tryDispatchFlattened)
    end valueDispatchings

    val moduleDispatching =
      nestedMultitierModules(module.symbol, module.pos.firstCodeLine).toList flatMap: (name, path) =>
        multitierAccessPath(path, module.symbol, defn.AnyClass) match
          case Some(access) =>
            Some:
              (request: Term, signature: Term, path: Term, reference: Term) =>
                CaseDef(Literal(StringConstant(name)), guard = None, Select.unique(access, names.dispatch).appliedTo(request, signature, path, reference))
          case _ =>
            errorAndCancel("Unexpected shape of path to nested module.", position(path.symbol) getOrElse module.pos.firstCodeLine)
            None

    val body = module.body map:
      case stat: ClassDef =>
        synthesizedPlacedValues(stat.symbol).fold(stat): placedValues =>
          val valueDispatching = valueDispatchings.getOrElse(stat.symbol, List.empty)

          if valueDispatching.nonEmpty || placedValues.peer == defn.AnyClass && moduleDispatching.nonEmpty then
            val tpe = MethodType(
              List("request", "signature", "path", "reference"))(
              _ => List(types.messageBuffer, types.valueSignature, TypeRepr.of[List[String]], types.valueReference),
              _ => symbols.`try`.typeRef.appliedTo(types.messageBuffer))
            val symbol = newMethod(stat.symbol, names.dispatch, tpe, Flags.Synthetic | Flags.Override, Symbol.noSymbol)

            def body(argss: List[List[Tree]]) =
              val args @ List(request, signature, path, reference) = argss.head map { arg => Ref(arg.symbol) }: @unchecked
              val fallback = Select.unique(Super(This(stat.symbol), None), names.dispatch).appliedToArgs(args)
              val default = CaseDef(Wildcard(), guard = None, fallback)

              val (identifier, _) = synthesizeModuleSignature(module.symbol)

              val emptyPath = path.select(symbols.iterableIsEmpty)
              val matchingSignatures = Select.unique(signature.select(symbols.valueSignatureModule), "==").appliedTo(This(module.symbol).select(identifier))

              def valueDispatch = Match(
                signature.select(symbols.valueSignatureName),
                (valueDispatching map { _(symbol, request, reference) }) :+ default)

              def moduleDispatch = Match(
                path.select(symbols.listHead),
                (moduleDispatching map { _(request, signature, path.select(symbols.listTail), reference) }) :+ default)

              if placedValues.peer == defn.AnyClass then
                if valueDispatching.isEmpty then
                  If(emptyPath, fallback, moduleDispatch)
                else if moduleDispatching.isEmpty then
                  If(Select.unique(emptyPath, "&&").appliedTo(matchingSignatures), valueDispatch, fallback)
                else
                  If(emptyPath, If(matchingSignatures, valueDispatch, fallback), moduleDispatch)
              else
                If(Select.unique(emptyPath, "&&").appliedTo(matchingSignatures), valueDispatch, fallback)
            end body

            val dispatch = DefDef(symbol, argss => Some(body(argss)))

            ClassDef.copy(stat)(stat.name, stat.constructor, stat.parents, stat.self, stat.body :+ dispatch)

          else
            stat

      case stat =>
        stat
    end body

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, body)
  end generateDispatching
end Dispatch
