package loci
package embedding
package impl
package components

import runtime.Peer
import transmitter.RemoteAccessException
import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait Dispatch:
  this: Component & Commons & ErrorReporter & Placements & PlacedValueSynthesis & RemoteAccessorSynthesis =>
  import quotes.reflect.*

  private enum Arguments[Result](val take: (Term => Term) => Option[Result], val ignore: Term => Result):
    case Populated extends Arguments(Some(_), Function.const(_))
    case Void extends Arguments(Function.const(None), identity)

  private def argumentApplication[Result](value: Term, arguments: Arguments[Result], argumentsType: TypeRepr) =
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
        errorAndCancel("Unexpected shape of placed value.", Position.ofMacroExpansion)
        None

      case _ =>
        Option.when(argumentTypes.isEmpty) { List.empty }
    end argumentApplication

    val application = argumentApplication(value.tpe.widenTermRefByName, untupledArgumentTypes, 0)

    if application.isEmpty && !canceled then
      errorAndCancel("Unexpected type of remote accessor.", Position.ofMacroExpansion)

    application flatMap: args =>
      arguments match
        case Arguments.Populated => arguments.take(arguments => value.appliedToArgss(args map { _ map { _(arguments) } }))
        case Arguments.Void => Some(arguments.ignore(value.appliedToArgss(args)))
  end argumentApplication

  private def argumentApplicationWithSubjectivity[Result](module: Symbol, owner: Symbol, value: Term, tpe: TypeRepr, arguments: Arguments[Result], argumentsType: TypeRepr, reference: Term) =
    def argumentApplicationWithSubjectivity(application: Term) =
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
    end argumentApplicationWithSubjectivity

    argumentApplication(value, arguments, argumentsType) flatMap: application =>
      arguments match
        case Arguments.Populated => arguments.take(arguments => argumentApplicationWithSubjectivity(application(arguments)))
        case Arguments.Void => Some(arguments.ignore(argumentApplicationWithSubjectivity(application)))
  end argumentApplicationWithSubjectivity

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
    extension (self: Map[Symbol, List[(Symbol, Term, Term, Term, Term) => Option[CaseDef]]])
      inline def prepend(symbol: Symbol)(term: (Symbol, Term, Term, Term, Term) => Option[CaseDef]) =
        self + (symbol -> (term :: self.getOrElse(symbol, List.empty)))

    val dispatching =
      synthesizeAccessors(module.symbol).placed.foldRight(Map.empty[Symbol, List[(Symbol, Term, Term, Term, Term) => Option[CaseDef]]]):
        case ((key, (placed, _)), dispatching) =>
          val symbol = key match
            case index: Int => module.symbol.methodMember(s"${names.block}$index").head
            case symbol: Symbol @unchecked => symbol

          synthesizedDefinitions(symbol).fold(dispatching): definition =>
            definition.impls.foldRight(dispatching): (impl, dispatching) =>
              dispatching.prepend(impl.owner): (owner, request, signature, path, reference) =>
                val value = This(impl.owner).select(definition.binding)
                val placedValue = This(module.symbol).select(placed)
                val argumentsType = placedValue.tpe.widenTermRefByName.typeArgs.head
                val placedType = symbol.info.widenTermRefByName.resultType

                val meaningfulArgument = meaningfulArgumentType(argumentsType)

                def result(value: Term) =
                  placedValue.select(symbols.placedValueResult).select(symbols.marshal).appliedTo(value, reference)

                def argumentApplication[Result](arguments: Arguments[Result]) =
                  argumentApplicationWithSubjectivity(module.symbol, impl.owner, value, placedType, arguments, argumentsType, reference)

                val dispatch =
                  if meaningfulArgument then
                    argumentApplication(Arguments.Populated) map: argumentApplication =>
                      placedValue.select(symbols.placedValueArguments).select(symbols.unmarshal).appliedTo(request, reference)
                        .select(symbols.tryMap)
                        .appliedToType(types.messageBuffer)
                        .appliedTo(
                          Lambda(
                            owner,
                            MethodType(List("arguments"))(_ => List(argumentsType), _ => types.messageBuffer),
                            (_, args) => result(argumentApplication(Ref(args.head.symbol)))))
                  else
                    argumentApplication(Arguments.Void) map: argumentApplication =>
                      result(argumentApplication)

                dispatch map: dispatch =>
                  val tpe =
                    if meaningfulArgument then
                      symbols.`try`.typeRef.appliedTo(types.messageBuffer)
                    else
                      types.messageBuffer

                  val tryDispatch =
                    Select.unique(Ref(symbols.`try`.companionModule), names.apply).appliedToType(tpe).appliedTo(dispatch)

                  val tryDispatchFlattened =
                    if meaningfulArgument then
                      tryDispatch.select(symbols.tryFlatten).appliedToType(types.messageBuffer).appliedTo(tryMessageBufferRefl)
                    else
                      tryDispatch

                  CaseDef(placedValue.select(symbols.placedValueSignature).select(symbols.valueSignatureName), guard = None, tryDispatchFlattened)
    end dispatching

    val body = module.body map:
      case stat: ClassDef =>
        synthesizedPlacedValues(stat.symbol).fold(stat): placedValues =>
          val tpe = MethodType(
            List("request", "signature", "path", "reference"))(
            _ => List(types.messageBuffer, types.valueSignature, TypeRepr.of[List[String]], types.valueReference),
            _ => symbols.`try`.typeRef.appliedTo(types.messageBuffer))
          val symbol = newMethod(stat.symbol, names.dispatch, tpe, Flags.Synthetic | Flags.Override, Symbol.noSymbol)
          val dispatch = DefDef(
            symbol,
            argss =>
              val args @ List(request, signature, path, reference) = argss.head map { arg => Ref(arg.symbol) }: @unchecked
              val default = CaseDef(Wildcard(), guard = None, Select.unique(Super(This(stat.symbol), None), names.dispatch).appliedToArgs(args))
              val cases = (dispatching.get(stat.symbol) getOrElse List.empty flatMap { _(symbol, request, signature, path, reference) }) :+ default
              Some(Match(signature.select(symbols.valueSignatureName), cases)))
          ClassDef.copy(stat)(stat.name, stat.constructor, stat.parents, stat.self, stat.body :+ dispatch)
      case stat =>
        stat

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, body)
  end generateDispatching
end Dispatch
