package loci
package embedding
package impl
package components

import utility.noMacroCheck
import utility.reflectionExtensions.*
import language.AccessorGeneration.*

import java.lang.reflect.Method
import java.util.IdentityHashMap
import scala.annotation.experimental
import scala.annotation.unchecked.uncheckedVariance
import scala.collection.immutable.SeqMap
import scala.collection.mutable
import scala.math.Ordering
import scala.util.control.NonFatal

object RemoteAccessorSynthesis:
  private val synthesizedModuleSignatureCache = Cache[Any, Any]
  private val synthesizedPeerSignatureCache = Cache.Layered[Any, Any, Any]
  private val synthesizedAccessorsCache = Cache.Tiered[Any, Any]

@experimental
trait RemoteAccessorSynthesis:
  this: Component & Commons & ErrorReporter & Placements & Peers & Annotations & SymbolTrees =>
  import quotes.reflect.*

  case class Accessors(
    identifier: (Symbol, Option[ValDef]),
    signature: (Symbol, Option[ValDef]),
    peers: SeqMap[Symbol, (Symbol, Option[ValDef], Symbol, Option[DefDef])],
    overridden: List[(Symbol, Option[ValDef])],
    marshalling: CachedTypeSeqMap[(Symbol, Option[ValDef])],
    placed: SeqMap[Symbol | Int, (Symbol, Option[ValDef])])

  private val synthesizedModuleSignatureCache = RemoteAccessorSynthesis.synthesizedModuleSignatureCache match
    case cache: Cache[Symbol, (Symbol, Symbol)] @unchecked => cache
  private val synthesizedPeerSignatureCache = RemoteAccessorSynthesis.synthesizedPeerSignatureCache match
    case cache: Cache.Layered[Symbol, Symbol, (Symbol, Symbol)] @unchecked => cache
  private val synthesizedAccessorsCache = RemoteAccessorSynthesis.synthesizedAccessorsCache match
    case cache: Cache.Tiered[Symbol, Accessors] @unchecked => cache

  private inline def infoArguments(symbol: Symbol, assertArgumentCount: Int) =
    val paramss = symbol.primaryConstructor.paramSymss
    assert(paramss.sizeIs == 1)
    assert(paramss.head.sizeIs == assertArgumentCount)
    paramss.head map { _.name }

  private val placedValueInfoArguments = infoArguments(symbols.placedValueInfo, assertArgumentCount = 3)
  private val marshallableInfoArguments = infoArguments(symbols.marshallableInfo, assertArgumentCount = 4)

  private def placedValueInfo(signature: String, arguments: String, result: String) =
    val args = placedValueInfoArguments lazyZip List(signature, arguments, result) map: (arg, value) =>
      NamedArg(arg, Literal(StringConstant(value)))
    New(TypeIdent(symbols.placedValueInfo)).select(symbols.placedValueInfo.primaryConstructor).appliedToArgs(args)

  private def marshallableInfo(signature: String, base: String, result: String, proxy: String) =
    val args = marshallableInfoArguments lazyZip List(signature, base, result, proxy) map: (arg, value) =>
      NamedArg(arg, Literal(StringConstant(value)))
    New(TypeIdent(symbols.marshallableInfo)).select(symbols.marshallableInfo.primaryConstructor).appliedToArgs(args)

  def meaningfulArgumentType(tpe: TypeRepr) =
    tpe.typeSymbol != defn.UnitClass && tpe.typeSymbol != defn.NullClass && tpe.typeSymbol != defn.NothingClass

  def synthesizeModuleSignature(module: Symbol): (Symbol, Symbol) =
    synthesizedModuleSignatureCache.getOrElseUpdate(module):
      val hasMultitierParent = module.typeRef.baseClasses.tail.foldLeft(false): (hasMultitierParent, parent) =>
        if isMultitierModule(parent) then
          synthesizeModuleSignature(parent)
          true
        else
          hasMultitierParent
      val flags = Flags.Lazy | (if hasMultitierParent then Flags.Override else Flags.EmptyFlags)
      val identifier = newVal(module, names.module, TypeRepr.of[String], flags, Symbol.noSymbol)
      val signature = newVal(module, names.signature, types.moduleSignature, flags, Symbol.noSymbol)
      SymbolMutator.getOrErrorAndAbort.enter(module, identifier)
      SymbolMutator.getOrErrorAndAbort.enter(module, signature)
      (identifier, signature)

  def synthesizePeerSignature(module: Symbol, peer: Symbol): (Symbol, Symbol) =
    synthesizedPeerSignatureCache.getOrElseUpdate(module, peer):
      val overridden = (peer.allOverriddenSymbols map { peer => peer.owner -> peer }).toMap + (peer.owner -> peer)
      val isOverriddingPeer = module.typeRef.baseClasses.tail.foldLeft(false): (isOverriddingPeer, parent) =>
        if isMultitierModule(parent) then
          val peer = overridden.get(parent)
          peer foreach { synthesizePeerSignature(parent, _) }
          isOverriddingPeer || peer.isDefined
        else
          isOverriddingPeer
      val overridingFlags = if isOverriddingPeer then Flags.Override else Flags.EmptyFlags
      val info = ByNameType(symbols.map.typeRef.appliedTo(List(types.peerSignature, types.peerTie)))
      val signature = newVal(module, s"${names.peerSignature}${peer.name}", types.peerSignature, Flags.Lazy | overridingFlags, Symbol.noSymbol)
      val ties = newMethod(module, s"${names.peerTies}${peer.name}", info, overridingFlags, Symbol.noSymbol)
      SymbolMutator.getOrErrorAndAbort.enter(module, signature)
      SymbolMutator.getOrErrorAndAbort.enter(module, ties)
      (signature, ties)

  private def injectFieldSymbol(symbol: Symbol) =
    val declared = symbol.owner.declaredField(symbol.name)
    if declared.exists then
      SymbolMutator.getOrErrorAndAbort.replace(symbol.owner, declared, symbol)
    else
      SymbolMutator.getOrErrorAndAbort.enter(symbol.owner, symbol)

  private val PureInterfaceFlag =
    try
      val flagsClass = Class.forName("dotty.tools.dotc.core.Flags$")
      val flags = flagsClass.getField("MODULE$")
      val pureInterface = flagsClass.getMethod("PureInterface")
      pureInterface.invoke(flags.get(null)) match
        case pureInterface: Flags @unchecked if Flags.EmptyFlags.getClass.isInstance(pureInterface) => Some(pureInterface)
        case _ => None
    catch
      case NonFatal(_) => None

  private def encodeName(name: String) = name flatMap:
    case '~' => "$tilde"
    case '=' => "$eq"
    case '<' => "$less"
    case '>' => "$greater"
    case '!' => "$bang"
    case '#' => "$hash"
    case '%' => "$percent"
    case '^' => "$up"
    case '&' => "$amp"
    case '|' => "$bar"
    case '*' => "$times"
    case '/' => "$div"
    case '+' => "$plus"
    case '-' => "$minus"
    case ':' => "$colon"
    case '?' => "$qmark"
    case '@' => "$at"
    case '\\' => "$bslash"
    case c => if !Character.isJavaIdentifierPart(c) then f"$$u${c.toInt}%04X" else c.toString

  private def classFileName(symbol: Symbol) =
    constructFullName(symbol,
      name = symbol => encodeName(targetName(symbol)),
      separator = symbol => if symbol.isPackageDef then "." else "$",
      skip = _.isPackageObject)

  private def showType(tpe: TypeRepr) = tpe match
    case TypeBounds(low, hi) if low.typeSymbol == defn.NothingClass && hi.typeSymbol == defn.AnyClass => "?"
    case _ => tpe.prettyShow

  private case class TransmittableTypes(base: TypeRepr, intermediate: TypeRepr, result: TypeRepr, proxy: TypeRepr, transmittables: TypeRepr):
    def typeList = List(base, intermediate, result, proxy, transmittables)
    def asMarshallableTypes = MarshallableTypes(base, result, proxy)
    def show = s"Transmittable[${showType(base)}, ${showType(intermediate)}, ${showType(result)}]"
    def showMore = s"$show { type Proxy = ${showType(proxy)} }"

  private object TransmittableTypes:
    def apply(transmittable: TypeRepr): TransmittableTypes =
      val resultType = transmittable.resultType
      val tpe =
        if resultType derivesFrom symbols.transmittable then
          resultType.select(symbols.`type`).dealias
        else
          resultType
      val typeArgs =
        List(symbols.base, symbols.intermediate, symbols.result, symbols.proxy, symbols.transmittables) map: member =>
          tpe.resolvedMemberType(member) getOrElse TypeRepr.of[Any] match
            case TypeBounds(low, hi) if low =:= hi => low
            case TypeBounds(low, hi) if low.typeSymbol == defn.NothingClass => hi
            case TypeBounds(low, hi) if hi.typeSymbol == defn.AnyClass => low
            case tpe => tpe
      val List(base, intermediate, result, proxy, transmittables) = typeArgs: @unchecked
      TransmittableTypes(base, intermediate, result, proxy, transmittables)

  private case class MarshallableTypes(base: TypeRepr, result: TypeRepr, proxy: TypeRepr):
    def typeList = List(base, result, proxy)
    def show = s"Marshallable[${showType(base)}, ${showType(result)}, ${showType(proxy)}]"

  private object MarshallableTypes:
    def apply(marshallable: TypeRepr): MarshallableTypes =
      val List(base, result, proxy) = marshallable.resultType.baseType(symbols.marshallable).typeArgs: @unchecked
      MarshallableTypes(base, result, proxy)

  private case class Transmittable(tree: Term, types: TransmittableTypes, signature: String)

  private object Transmittable:
    def apply(tree: Term): Transmittable =
      Transmittable(tree, TransmittableTypes(tree.tpe), transmittableSignature(tree))

  private case class Marshallable(symbol: Symbol, types: MarshallableTypes, signature: String)

  private object Marshallable:
    def apply(symbol: Symbol, module: Symbol): Option[Marshallable] =
      marshallableInfo(symbol) map : (signature, _, _, _) =>
        Marshallable(symbol, MarshallableTypes(ThisType(module).select(symbol)), signature)
    def predefined(symbol: Symbol): Marshallable =
      Marshallable(symbol, MarshallableTypes(symbol.typeRef), unknownSignature)

  private class AccessorResolution(var transmittable: Option[Transmittable], var marshallable: Option[Option[(Marshallable, Either[Symbol, ValDef])]], var allowSkippingAbstract: Boolean):
    def this(transmittable: Option[Transmittable], marshallable: Option[Option[(Marshallable, Either[Symbol, ValDef])]]) = this(transmittable, marshallable, true)
    def this() = this(None, None, true)

  sealed class CachedTypeSeqMap[+T]:
    protected var map: mutable.Map[TypeRepr, T] @uncheckedVariance = mutable.Map.empty
    protected var list: mutable.ListBuffer[T] @uncheckedVariance = mutable.ListBuffer.empty
    def lookupType(tpe: TypeRepr): Option[T] =
      map.get(tpe) orElse:
        map find { (key, _) => key =:= tpe } map: (_, value) =>
          map += tpe -> value
          value
    def iterator: Iterator[T] =
      list.iterator
    def mapValues[U](f: T => U): CachedTypeSeqMap[U] =
      flatMapValues { v => Some(f(v)) }
    def flatMapValues[U](f: T => Option[U]): CachedTypeSeqMap[U] =
      val other = CachedTypeSeqMap[U]
      other.list.sizeHint(list)
      other.map.sizeHint(map.size)
      val mapping = IdentityHashMap[T, Option[U]]
      list foreach: value =>
        mappedValue(value, f, mapping) foreach: value =>
          other.list += value
      map foreach: (key, value) =>
        mapping.get(value) foreach: value =>
          other.map += key -> value
      other
    protected def mappedValue[T, U](value: T, f: T => Option[U], mapping: IdentityHashMap[T, Option[U]]) =
      mapping.get(value) match
        case null =>
          val mapped = f(value)
          mapping.put(value, mapped)
          mapped
        case mapped =>
          mapped

  sealed class MutableCachedTypeSeqMap[T] extends CachedTypeSeqMap[T]:
    def addNewTypeEntry(tpe: TypeRepr, value: T): T =
      assert(lookupType(tpe).isEmpty)
      map += tpe -> value
      list += value
      value
    def mapValuesInPlace(f: T => T): this.type =
      flatMapValuesInPlace { v => Some(f(v)) }
      this
    def flatMapValuesInPlace(f: T => Option[T]): this.type =
      val mapping = IdentityHashMap[T, Option[T]]
      list flatMapInPlace { mappedValue(_, f, mapping) }
      map filterInPlace { (_, value) => mapping.get(value).isDefined } mapValuesInPlace { (_, value) => mapping.get(value).get }
      this

  private val placedBlockSignature = "\\d>".r.unanchored

  private def argumentTypes(tpe: TypeRepr): List[List[TypeRepr]] = tpe match
    case MethodType(_, paramTypes, resType) =>
      paramTypes :: argumentTypes(resType)
    case PolyType(_, _, resType) =>
      argumentTypes(resType)
    case _ =>
      List.empty

  private def serializeTypeAndSanityCheck(tpe: TypeRepr, from: Symbol) =
    TypeToken.fromType(tpe, from) flatMap: tokens =>
      val serialized = TypeToken.serialize(tokens)
      Option.when(TypeToken.deserializeType(serialized, from) exists { _ =:= tpe }):
        (tokens, serialized)

  private def mangledSymbolName(symbol: Symbol) =
    f"${s"${implementationForm(symbol)} ${fullName(symbol)}".hashCode}%08x"

  private def implementationForm(symbol: Symbol) =
    if symbol.flags is Flags.Module then "object"
    else if symbol.flags is Flags.Trait then "trait"
    else "class"

  private def accessorSignaturePrefix(module: Symbol) =
    val signature = TypeToken.typeSignature(module.typeRef)
    if signature.takeRight(2) == TypeToken.`type` then signature.init else signature :+ TypeToken.`#`

  private def accessorSignature(name: List[TypeToken], params: List[List[TypeRepr]], result: TypeRepr) =
    val paramsSignature = params flatMap: params =>
      TypeToken.`(` :: ((params flatMap { param => TypeToken.`,` ++ TypeToken.typeSignature(param) }).drop(2) :+ TypeToken.`)`)
    val signature = name ++ paramsSignature ++ TypeToken.`:` ++ TypeToken.typeSignature(result)
    TypeToken.serialize(signature)

  private val unknownSignature = "########"

  private val abstractSignature = "abstract"

  private def transmittableSignature(term: Term) =
    TermToken.serializeTerm(term).toOption.fold(unknownSignature): term =>
      f"${term.hashCode}%08x"

  private def annotationStrings(args: List[Term], names: List[String]) =
    def annotationStrings(args: List[Term], names: List[String], namedArgsRequired: Boolean): Option[Map[String, String]] =
      (args, names) match
        case (MaybeInlined(NamedArg(name, MaybeInlined(Literal(StringConstant(value))))) :: args, _ :: names) =>
          annotationStrings(args, names, namedArgsRequired = true) map { _ + (name -> value) }
        case (MaybeInlined(Literal(StringConstant(value))) :: args, name :: names) if !namedArgsRequired =>
          annotationStrings(args, names, namedArgsRequired = false) map { _ + (name -> value) }
        case _ =>
          Option.when(args.isEmpty && names.isEmpty) { Map.empty }

    annotationStrings(args, names, namedArgsRequired = false) map { names map _ }
  end annotationStrings

  private def placedInfo(symbol: Symbol) =
    symbol.getAnnotation(symbols.placedValueInfo) match
      case Some(Apply(_, args)) =>
        annotationStrings(args, placedValueInfoArguments) map: args =>
          val List(signature, arguments, result) = args
          (signature, arguments, result)
      case _ =>
        None

  private def marshallableInfo(symbol: Symbol) =
    symbol.getAnnotation(symbols.marshallableInfo) match
      case Some(Apply(_, args)) =>
        annotationStrings(args, marshallableInfoArguments) map: args =>
          val List(signature, base, result, proxy) = args
          (signature, base, result, proxy)
      case _ =>
        None

  private val predefinedMarshallables =
    List(symbols.marshallableUnit, symbols.marshallableNull, symbols.marshallableNothing) map Marshallable.predefined

  private def marshallingIdentifier(name: String) =
    val identifier = name.stripPrefix(names.marshalling).replace('$', ':')
    if identifier.length != name.length then identifier else s"<$identifier>"

  private def marshallingName(name: String) =
    if name.length > 1 && name.head == '<' && name.last == '>' then
      name.substring(1, name.length - 1)
    else
      s"${names.marshalling}${name.replace(':', '$')}"

  private object PlacedBlock:
    def unapply(term: Term) = term match
      case Apply(Apply(invocation @ TypeApply(Select(prefix, _), _ :: value :: _), List(lambda @ Lambda(List(_), block))), _)
          if term.symbol.maybeOwner == symbols.block && lambda.tpe.isContextFunctionType =>
        val captures =
          prefix match
            case Apply(_, VarArgs(captures)) if prefix.symbol.maybeOwner == symbols.capture => captures
            case _ => List.empty
        Some(value.tpe, captures map { _.tpe.widenTermRefByName }, invocation.posInUserCode)
      case _ =>
        None

  private object PlacedBlockInvocation:
    def unapply(term: Term) = term match
      case PlacedAccess(_, _, term @ PlacedBlock(value, captures, pos), _, _, _, _) => Some(term, value, captures, pos)
      case PlacedBlock(_, captures, pos) => Some(term, TypeRepr.of[Unit], captures, pos)
      case _ => None

  private object typeParamMasker:
    private var symbolSubstitutions = Map.empty[Symbol, Symbol]
    private var symbolSubstitutionsReverse = Map.empty[Symbol, TypeRepr]
    private var presentationSubstitutionsReverse = Map.empty[String, String]

    private object typeParamTypeMasker extends TypeMap(quotes):
      override def transform(tpe: TypeRepr) =
        val symbol = tpe.typeSymbol
        if symbol.isTypeParam then
          symbolSubstitutions.get(symbol) match
            case Some(abstractTypeSymbol) =>
              abstractTypeSymbol.typeRef
            case _ =>
              symbol.info match
                case TypeBounds(low, hi) if low =:= hi =>
                  transform(low)
                case TypeBounds(_, _) =>
                  val presentation = tpe.safeShow
                  val abstractTypePresentation = s"<Some Abstract Type: $presentation>"
                  val Inlined(_, _, Block(List(stat), _)) = '{ type `<Some Abstract Type>` }.asTerm
                  val abstractTypeSymbol = stat.symbol
                  SymbolMutator.get foreach { _.setTypeName(abstractTypeSymbol, abstractTypePresentation) }
                  symbolSubstitutions += symbol -> abstractTypeSymbol
                  symbolSubstitutionsReverse += abstractTypeSymbol -> tpe
                  presentationSubstitutionsReverse += abstractTypePresentation -> presentation
                  abstractTypeSymbol.typeRef
                case info @ (
                    _: NamedType | _: ParamRef | _: ThisType | _: SuperType | _: AppliedType |
                    _: Refinement | _: AndOrType | _: AnnotatedType | _: MatchType | _: ByNameType |
                    _: LambdaType | _: RecursiveType | _: RecursiveThis | _: ConstantType) =>
                  transform(info)
                case _ =>
                  super.transform(tpe)
        else
          super.transform(tpe)
    end typeParamTypeMasker

    private object typeParamTypeUnmasker extends TypeMap(quotes):
      override def transform(tpe: TypeRepr) =
        symbolSubstitutionsReverse.getOrElse(tpe.typeSymbol, super.transform(tpe))

    private object typeParamTermUnmasker extends SafeTreeMap(quotes):
      override def transformTypeTree(tree: TypeTree)(owner: Symbol) = tree match
        case Inferred() =>
          val tpe = typeParamTypeUnmasker.transform(tree.tpe)
          if tpe != tree.tpe then TypeTree.of(using tpe.asType) else tree
        case TypeIdent(_) | TypeSelect(_, _) =>
          symbolSubstitutionsReverse.get(tree.tpe.typeSymbol) match
            case Some(tpe) if tpe != tree.tpe => TypeTree.of(using tpe.asType)
            case _ => super.transformTypeTree(tree)(owner)
        case _ =>
          super.transformTypeTree(tree)(owner)

    def mask(tpe: TypeRepr): TypeRepr =
      typeParamTypeMasker.transform(tpe)

    def unmask(term: Term): Term =
      typeParamTermUnmasker.transformTerm(term)(Symbol.spliceOwner)

    def unmask(presentation: String): String =
      presentationSubstitutionsReverse.foldLeft(presentation):
        case (current, (presentation, abstractTypePresentation)) => current.replace(presentation, abstractTypePresentation)

    def masked(symbol: Symbol): Boolean =
      symbolSubstitutionsReverse contains symbol

    def clear(): Unit =
      symbolSubstitutions = Map.empty
      symbolSubstitutionsReverse = Map.empty
      presentationSubstitutionsReverse = Map.empty
  end typeParamMasker

  private object Resolution:
    enum Result:
      case Success(term: Term)
      case Failure(message: String)
      case FailureOnTypeParameter(message: String, term: Term)

    object Result:
      def apply(tree: Term) =
        def withPeriod(message: String) =
          val stripped = message.strip
          if stripped.nonEmpty && stripped.last == '.' then stripped else stripped + '.'
        resolutionFailureCollector.foldTree(None, tree)(Symbol.noSymbol) match
          case Some(message, false) => Failure(withPeriod(message))
          case Some(message, true) => FailureOnTypeParameter(withPeriod(message), tree)
          case _ => Success(tree)

      extension (self: Result)
        def asTransmittable(allowFailureForTypeParameters: Boolean) = self match
          case Success(term) =>
            Right(Transmittable(term))
          case Failure(message) =>
            Left(message)
          case FailureOnTypeParameter(message, term) =>
            Either.cond(
              allowFailureForTypeParameters,
              Transmittable(term, TransmittableTypes(term.tpe), abstractSignature),
              message)

        def asTerm = self match
          case Success(term) => Right(term)
          case Failure(message) => Left(message)
          case FailureOnTypeParameter(message, _) => Left(message)
    end Result

    private object resolutionFailureCollector extends TreeAccumulator[Option[(String, Boolean)]]:
      def foldTree(failure: Option[(String, Boolean)], tree: Tree)(owner: Symbol) = tree match
        case Block(List(defintion @ DefDef(names.resolutionFailure, _, _, _), Apply(call, List())), expr) if defintion.symbol == call.symbol =>
          compileTimeOnly(defintion.symbol).fold(foldOverTree(failure, tree)(owner)): message =>
            val typeSymbol = TransmittableTypes(expr.tpe).base.typeSymbol
            val typeParam = typeSymbol.isTypeParam || (typeParamMasker masked typeSymbol)
            failure match
              case Some(_, false) => failure
              case Some(_, true) if typeParam => foldOverTree(failure, tree)(owner)
              case _ if typeParam => foldOverTree(Some(typeParamMasker.unmask(message), typeParam), tree)(owner)
              case _ => Some(typeParamMasker.unmask(message), typeParam)
        case _ =>
          foldOverTree(failure, tree)(owner)

    private val cache = MutableCachedTypeSeqMap[Result]

    def resolve(tpe: TypeRepr, message: String) =
      cache.lookupType(tpe) getOrElse:
        val result =
          noMacroCheck(Implicits.search(typeParamMasker.mask(tpe))) match
            case result: ImplicitSearchSuccess => Result(typeParamMasker.unmask(result.tree))
            case _ => Result.Failure(typeParamMasker.unmask(message))
        cache.addNewTypeEntry(tpe, result)
        result

    def resolveSerializable(tpe: TypeRepr) =
      resolve(
        symbols.serializable.typeRef.appliedTo(tpe),
        s"${prettyType(tpe.prettyShow)} is not serializable.").asTerm

    def resolveTransmittable(tpe: TypeRepr, allowFailureForTypeParameters: Boolean) =
      resolve(
        symbols.transmittable.typeRef.appliedTo(List(tpe, TypeBounds.empty, TypeBounds.empty, TypeBounds.empty, TypeBounds.empty)),
        s"${prettyType(tpe.prettyShow)} is not transmittable.").asTransmittable(allowFailureForTypeParameters)
  end Resolution

  private def signatures(module: Symbol) =
    extension (tpe: TypeRepr)
      def asTerm: Option[Term] = tpe match
        case AnnotatedType(underlying, _) => underlying.asTerm
        case Refinement(parent, _, _) => parent.asTerm
        case ThisType(tref) => Some(This(tref.typeSymbol))
        case TermRef(NoPrefix(), name) => Some(Ref(tpe.termSymbol))
        case TermRef(qualifier, name) => qualifier.asTerm map { Select.unique(_, name) }
        case _ => None

      def pathTerm: Option[Term] = tpe match
        case tpe: AnnotatedType => tpe.underlying.pathTerm
        case tpe: Refinement => tpe.parent.pathTerm
        case tpe: NamedType => tpe.qualifier.asTerm
        case _ => None
    end extension

    def signature(peerType: TypeRepr) =
      peerType.pathTerm match
        case Some(term) if isMultitierModule(term.symbol) =>
          val(symbol, _) = synthesizePeerSignature(peerType.typeSymbol.owner, peerType.typeSymbol)
          Some(term.select(symbol))
        case _ =>
          val splicePos = Position.ofMacroExpansion
          val pos = peerType.typeSymbol.pos match
            case Some(pos) if pos.sourceFile == splicePos.sourceFile && pos.start >= splicePos.start && pos.end <= splicePos.end =>
              pos
            case _ =>
              splicePos
          errorAndCancel(s"Invalid prefix for peer type: ${prettyType(peerType.prettyShow)}", pos)
          None

    val moduleIdentifier =
      val (symbol, _) = synthesizeModuleSignature(module)
      ValDef(symbol, Some(Literal(StringConstant(fullName(module)))))

    val moduleSignature =
      val (_, symbol) = synthesizeModuleSignature(module)
      val name = if module.isClassDef && module.isModuleDef then module.companionModule.name else module.name
      val rhs = module.owner findAncestor isMultitierModule match
        case Some(outer) =>
          val (symbol, _) = synthesizeAccessors(outer).signature
          Ref(symbols.moduleSignatureNested).appliedTo(This(outer).select(symbol), Literal(StringConstant(name)))
        case _ =>
          Ref(symbols.moduleSignature).appliedTo(Literal(StringConstant(name)))
      ValDef(symbol, Some(rhs))

    val peerSignatures =
      PeerInfo.ofModule(module).iterator flatMap: peerInfo =>
        val peer = peerInfo.peerType.typeSymbol
        if peer != defn.AnyClass then
          val parents = peerInfo.parents flatMap signature

          val parentList = Typed(
            Repeated(parents, TypeTree.of(using types.peerSignature.asType)),
            TypeTree.of(using symbols.repeated.typeRef.appliedTo(types.peerSignature).asType))

          val signatureConstruction =
            Ref(symbols.peerSignature).appliedTo(
              Literal(StringConstant(peer.name)),
              Select.unique(Ref(symbols.list.companionModule), names.apply)
                .appliedToType(types.peerSignature)
                .appliedTo(parentList),
              Ref(moduleSignature.symbol))

          val ties = peerInfo.ties flatMap: (tie, multiplicity) =>
            signature(tie) map: tie =>
              multiplicity match
                case Multiplicity.Single => Tuple(List(tie, Ref(symbols.peerTieSingle)))
                case Multiplicity.Optional => Tuple(List(tie, Ref(symbols.peerTieOptional)))
                case Multiplicity.Multiple => Tuple(List(tie, Ref(symbols.peerTieMultiple)))

          val tieList = Typed(
            Repeated(ties, TypeTree.of(using Tuple(List(types.peerSignature, types.peerTie)).asType)),
            TypeTree.of(using symbols.repeated.typeRef.appliedTo(Tuple(List(types.peerSignature, types.peerTie))).asType))

          val tiesConstruction =
            Select.unique(Ref(symbols.map.companionModule), names.apply)
              .appliedToTypes(List(types.peerSignature, types.peerTie))
              .appliedTo(tieList)

          val (signatureSymbol, tiesSymbol) = synthesizePeerSignature(module, peer)

          Some(
            peer ->
            (signatureSymbol,
             Some(ValDef(signatureSymbol, Some(signatureConstruction))),
             tiesSymbol,
             Some(DefDef(tiesSymbol, _ => Some(tiesConstruction)))))
        else
          None
    end peerSignatures

    ((moduleIdentifier.symbol, Some(moduleIdentifier)),
     (moduleSignature.symbol, Some(moduleSignature)),
     peerSignatures.to(SeqMap))
  end signatures

  private def synthesizeAllPlacedAccessors(symbol: Symbol, includeFirst: Boolean): Map[Int | Symbol, Symbol] =
    val baseClasses = symbol.typeRef.baseClasses
    val placedTail = baseClasses.tail.reverseIterator flatMap: base =>
      if isMultitierModule(base) then
        synthesizeAccessors(base).placed.iterator flatMap:
          case (_: Int, _) => None
          case (original, (placed, _)) => Some(original -> placed)
      else
        Iterator.empty
    val placedHead =
      if includeFirst && isMultitierModule(baseClasses.head) then
        synthesizeAccessors(baseClasses.head).placed.iterator map:
          case (original, (placed, _)) => original -> placed
      else
        Iterator.empty
    (placedTail ++ placedHead).toMap

  def synthesizeAllPlacedAccessors(symbol: Symbol): Map[Int | Symbol, Symbol] =
    synthesizeAllPlacedAccessors(symbol, includeFirst = true)

  def synthesizeAllPeerSignatures(symbol: Symbol): Map[Symbol, Symbol] =
    (synthesizeAccessors(symbol).peers.view mapValues { (signature, _ , _, _) => signature }).toMap

  def synthesizeAccessors(symbol: Symbol): Accessors =
    val module = if symbol.moduleClass.exists then symbol.moduleClass else symbol
    val originalTree = if module.pos exists { _.sourceFile == SourceFile.current } then symbolOriginalTree(module) else None
    val tier = if originalTree.isDefined then 1 else 0

    synthesizedAccessorsCache.getOrElseUpdate(module, tier):
      // `Class.forName` may throw a `ClassNotFoundException` if the required class file has not yet been generated yet.
      // In such cases, the compiler suspends the compilation unit temporarily to allow the generation of the missing class file.
      // Once the dependency is available, the compilation unit is retried.
      val accessors = originalTree match
        case Some(tree: ClassDef) => synthesizeAccessorsFromTree(module, tree)
        case _ => synthesizeAccessorsFromClass(module, Class.forName(classFileName(module)))

      if module.isModuleDef then
        synthesizedAccessorsCache.update(module.companionModule, accessors, tier)

      typeParamMasker.clear()

      accessors
  end synthesizeAccessors

  private def synthesizeAccessorsFromTree(module: Symbol, tree: ClassDef): Accessors =
    val mangledName = mangledSymbolName(module)
    val locallyScoped = module hasAncestor { symbol => symbol.isMethod || symbol.isField }
    val signaturePrefix = accessorSignaturePrefix(module)
    val (identifier @ (identifierSymbol, _), signature @ (signatureSymbol, _), peers) = signatures(module)

    val defaultAccessorGeneration = if module.flags is Flags.Final then Required else Preferred

    val accessorGeneration =
      multitierModuleArgument(module) match
        case Some(arg) =>
          val symbol = arg.symbol
          val accessorGeneration =
            if symbol == TypeRepr.of[Deferred.type].termSymbol then Deferred
            else if symbol == TypeRepr.of[Preferred.type].termSymbol then Preferred
            else if symbol == TypeRepr.of[Required.type].termSymbol then Required
            else if symbol == TypeRepr.of[Forced.type].termSymbol then Forced
            else
              errorAndCancel("Unexpected accessor generation mode.", arg.posInUserCode)
              defaultAccessorGeneration

          if (module.flags is Flags.Final) && accessorGeneration != Required && accessorGeneration != Forced then
            val impl = if module.isModuleDef then "objects" else "final classes"
            errorAndCancel(s"Accessor generation mode for $impl must be `Required` or `Forced`.", arg.posInUserCode)

          accessorGeneration
        case _ =>
          defaultAccessorGeneration
    end accessorGeneration

    val allowAbstractMarshallables = accessorGeneration == Deferred || accessorGeneration == Preferred

    def accessorGenerationFailureMessageProlog(symbolForName: Option[Symbol], symbolForParent: Option[Symbol], noninheritedPosition: Option[Position]) =
      val message = "Failed to generate accessor for"

      def signature(symbol: Symbol) =
        val paramSymss =
          if hasSyntheticMultitierContextArgument(symbol) then
            symbol.paramSymss.init
          else
            symbol.paramSymss
        val args =
          paramSymss map: params =>
            val args = params map: param =>
              param.info match
                case TypeBounds(low, hi) if low.typeSymbol == defn.NothingClass && hi.typeSymbol == defn.AnyClass => param.name
                case TypeBounds(low, hi) if low.typeSymbol == defn.NothingClass => s"${param.name} <: ${hi.prettyShowFrom(module)}"
                case TypeBounds(low, hi) if hi.typeSymbol == defn.AnyClass => s"${param.name} >: ${low.prettyShowFrom(module)}"
                case TypeBounds(low, hi) => s"${param.name} >: ${low.prettyShowFrom(module)} <: ${hi.prettyShowFrom(module)}"
                case tpe => s"${param.name}: ${tpe.prettyShowFrom(module)}"
            if params.isEmpty || params.head.isTerm then s"(${args.mkString(", ")})" else s"[${args.mkString(", ")}]"
        val result =
          val tpe = symbol.info.resultType
          PlacementInfo(tpe).fold(tpe.prettyShowFrom(module)) { _.showCanonicalFrom(module) }
        s"${args.mkString}: $result"

      val name = symbolForName match
        case Some(symbol) =>
          if symbol.name startsWith names.block then "remote block"
          else if symbol.isClassDef && symbol.isModuleDef then s"placed value ${symbol.companionModule.name}"
          else if symbol.isMethod && symbol.paramSymss.nonEmpty then s"placed value ${symbol.name}${signature(symbol)}"
          else s"placed value ${symbol.name}"
        case _ =>
          "remote block"

      noninheritedPosition match
        case Some(pos) =>
          (s"$message $name", pos)
        case _ =>
          val parent =
            symbolForParent flatMap: symbol =>
              tree.parents find { _.symbol == symbol.maybeOwner } orElse:
                tree.parents find: parent =>
                  (parent.symbol.fieldMembers contains symbol) ||
                  (parent.symbol.methodMembers contains symbol) ||
                  (parent.symbol.typeMembers contains symbol)
          parent.fold(s"$message inherited $name", tree.posInUserCode.firstCodeLine): parent =>
            symbolForParent match
              case Some(symbol) if parent.symbol == symbol.maybeOwner =>
                (s"$message $name, inherited from ${prettyType(parent.symbol.name)}", parent.posInUserCode)
              case Some(symbol) if symbol.maybeOwner.exists && symbol.maybeOwner.maybeOwner == module.maybeOwner =>
                (s"$message $name, defined in ${prettyType(symbol.maybeOwner.name)}, inherited through ${prettyType(parent.symbol.name)}", parent.posInUserCode)
              case Some(symbol) if symbol.maybeOwner.exists =>
                (s"$message $name, defined in ${prettyType(fullName(symbol.maybeOwner))}, inherited through ${prettyType(parent.symbol.name)}", parent.posInUserCode)
              case _ =>
                (s"$message $name, inherited through ${prettyType(parent.symbol.name)}", parent.posInUserCode)
    end accessorGenerationFailureMessageProlog

    def isLocalVariable(symbol: Symbol) =
      symbol hasAncestor module

    type AccessCollection = (List[TypeToken], Int, List[(Option[Symbol], String, TypeRepr, () => (String, Position))], List[(Term, Position)], Set[Symbol], IdentityHashMap[Term, Unit], Option[Position])

    object accessCollector extends TreeAccumulator[AccessCollection]:
      def foldTree(accesses: AccessCollection, tree: Tree)(owner: Symbol) =
        val (indexing, index, values, transmittables, accessed, blocks, pos) = accesses
        tree match
          case ValDef(_, tpt, rhs) if !(tpt.tpe =:= TypeRepr.of[Nothing]) && tpt.tpe <:< types.transmittable =>
            rhs.fold(accesses):
              foldOverTree((indexing, index, values, transmittables, accessed, blocks, pos), _)(owner)

          case DefDef(_, List() | List(List()), tpt, rhs) if !(tpt.tpe =:= TypeRepr.of[Nothing]) && tpt.tpe <:< types.transmittable =>
            rhs.fold(accesses):
              foldOverTree((indexing, index, values, transmittables, accessed, blocks, pos), _)(owner)

          case PlacedBlockInvocation(block, value, captures, position) if !(blocks containsKey block) =>
            val params = captures map { capture => PlacementInfo(capture).fold(capture) { _.valueType } }
            val signature = accessorSignature(indexing ++ List(TypeToken.number(index), TypeToken.`>`), List(params), value)
            val tpe = MethodType(captures.indices.toList map { index => s"arg$index" })(_ => params, _ => value)
            val prolog = () => accessorGenerationFailureMessageProlog(symbolForName = None, symbolForParent = None, noninheritedPosition = Some(position))
            blocks.put(block, ())
            foldOverTree((indexing, index + 1, (None, signature, tpe, prolog) :: values, transmittables, accessed, blocks, pos), tree)(owner)

          case PlacedAccess(_, _, PlacedValueReference(value, _), _, _, _, _) if value.symbol.exists =>
            foldOverTree((indexing, index, values, transmittables, accessed + value.symbol, blocks, pos), tree)(owner)

          case Apply(Apply(_, List(PlacedValueReference(value, _))), _) if tree.symbol.maybeOwner == symbols.call && value.symbol.exists =>
            foldOverTree((indexing, index, values, transmittables, accessed + value.symbol, blocks, pos), tree)(owner)

          case tree: Term if !(tree.tpe =:= TypeRepr.of[Nothing]) && tree.tpe <:< types.transmittable && !isLocalVariable(tree.symbol) =>
            val treePosition = tree.posInUserCode
            val position = if treePosition != Position.ofMacroExpansion then treePosition else pos getOrElse treePosition
            foldOverTree((indexing, index, values, (tree, position) :: transmittables, accessed, blocks, pos), tree)(owner)

          case Select(qualifier, _) =>
            val treePosition = tree.posInUserCode
            val position =
              Option.when(treePosition != Position.ofMacroExpansion):
                val qualifierPosition = qualifier.posInUserCode
                if treePosition != Position.ofMacroExpansion then
                  val offset = treePosition.sourceFile.content.fold(0): content =>
                    (content.substring(qualifierPosition.end).iterator takeWhile { c => c.isWhitespace || c == '.' }).size
                  Position(treePosition.sourceFile, qualifierPosition.end + offset, treePosition.end).lastCodeLine
                else
                  treePosition.lastCodeLine
            val accesses = foldOverTree((indexing, index, values, transmittables, accessed, blocks, position), tree)(owner)
            val prefix = accesses.take(accesses.size - 1)
            prefix :* pos

          case _ =>
            foldOverTree((indexing, index, values, transmittables, accessed, blocks, pos), tree)(owner)
    end accessCollector

    def collectAccesses(indexing: String | Int, tree: Tree, values: List[(Option[Symbol], String, TypeRepr, () => (String, Position))], transmittables: List[(Term, Position)], accessed: Set[Symbol]) =
      val signatureSuffix = List(TypeToken.`<`, TypeToken("placed"), TypeToken.` `, TypeToken("block"), TypeToken.` `)
      val init = indexing match
        case index: Int => (signaturePrefix ++ signatureSuffix, index)
        case name: String => (signaturePrefix ++ (TypeToken(name) :: signatureSuffix), 0)
      val (_, index, collectedValues, collectedTransmittables, collectedAccesses, _, _) =
        accessCollector.foldTree(init ++ (values, transmittables, accessed, IdentityHashMap[Term, Unit], None), tree)(module)
      (index, collectedValues, collectedTransmittables, collectedAccesses)

    val (_, values, transmittables, accessed) =
      tree.body.foldLeft(0, List.empty[(Option[Symbol], String, TypeRepr, () => (String, Position))], List.empty[(Term, Position)], Set.empty[Symbol]):
        case ((index, values, transmittables, accessed), stat @ (_: ValDef | _: DefDef))
            if (stat.symbol.isField || stat.symbol.isMethod) && !stat.symbol.isModuleDef =>
          val (tpt, rhs) = stat match
            case ValDef(_, tpt, rhs) => (tpt, rhs)
            case DefDef(_, _, tpt, rhs) => (tpt, rhs)

          val symbol = stat.symbol

          val (_, collectedValues, collectedTransmittables, collectedAccessed) =
            collectAccesses(targetName(symbol), stat, values, transmittables, accessed)

          val value = PlacementInfo(tpt.tpe) collect:
            case placementInfo if !placementInfo.modality.local =>
              val (paramSymss, info) =
                if hasSyntheticMultitierContextArgument(symbol) then
                  (symbol.paramSymss.init, dropLastArgumentList(symbol.info))
                else
                  (symbol.paramSymss, symbol.info)
              val params = paramSymss collect:
                case params if params.isEmpty || params.head.isTerm => params map { _.info }

              val prolog = () =>
                inline def posWithoutBody = rhs map: rhs =>
                  val start = rhs.posInUserCode.start
                  val offset = stat.pos.sourceFile.content.fold(0): content =>
                    (content.substring(0, start).reverseIterator takeWhile { c => c.isWhitespace || c == '=' }).size
                  Position(stat.pos.sourceFile, stat.posInUserCode.start, start - offset)

                val pos =
                  symbol.pos orElse
                  posWithoutBody getOrElse
                  Position(stat.pos.sourceFile, stat.posInUserCode.start, tpt.posInUserCode.end)

                accessorGenerationFailureMessageProlog(symbolForName = Some(symbol), symbolForParent = Some(symbol), noninheritedPosition = Some(pos))
              end prolog

              (Some(symbol),
               accessorSignature(signaturePrefix :+ TypeToken(targetName(symbol)), params, placementInfo.valueType),
               info.withResultType(placementInfo.valueType),
               prolog)
          end value

          def insertedIntoNonEmptyListBefore[T](list: List[T], element: T, before: List[T]): List[T] =
            if list eq before then element :: list else list.head :: insertedIntoNonEmptyListBefore(list.tail, element, before)

          val insertedValues =
            value.fold(collectedValues): value =>
              if collectedValues.isEmpty then List(value) else insertedIntoNonEmptyListBefore(collectedValues, value, values)

          (index, insertedValues, collectedTransmittables, collectedAccessed)

        case ((index, values, transmittables, accessed), stat: Term) =>
          collectAccesses(index, stat, values, transmittables, accessed)

        case (accesses, _) =>
          accesses
    end val

    val accessorResolutionTypeMap = MutableCachedTypeSeqMap[AccessorResolution]

    def incoherenceMessage(tpe: TypeRepr) =
      s"Incoherent transmittables for type ${prettyType(tpe.prettyShow)}"

    object localVariablesCollector extends TreeAccumulator[(Set[Symbol], Boolean)]:
      def foldTree(variables: (Set[Symbol], Boolean), tree: Tree)(owner: Symbol) =
        val (localVariables, accessesLocalVariable) = variables
        tree match
          case tree: Definition =>
            foldOverTree((localVariables + tree.symbol, accessesLocalVariable), tree)(owner)
          case tree if tree.symbol.exists =>
            val symbol = tree.symbol
            if accessesLocalVariable || (!(localVariables contains symbol) && isLocalVariable(symbol) && (symbol.isTerm || symbol.owner != module)) then
              (localVariables, true)
            else
              foldOverTree(variables, tree)(owner)
          case tree =>
            foldOverTree(variables, tree)(owner)

    transmittables.reverseIterator foreach: (tree, pos) =>
      if !canceled then
        val (_, accessesLocalVariable) = localVariablesCollector.foldTree((Set.empty, false), tree)(Symbol.noSymbol)
        val transmittable = Transmittable(tree)
        if !accessesLocalVariable then
          accessorResolutionTypeMap.lookupType(transmittable.types.base) match
            case Some(resolution) =>
              resolution.transmittable foreach: other =>
                if !(transmittable.tree.tpe =:= other.tree.tpe) || transmittable.signature != other.signature then
                  if !(transmittable.types.base =:= other.types.base) ||
                     !(transmittable.types.intermediate =:= other.types.intermediate) ||
                     !(transmittable.types.result =:= other.types.result) then
                    errorAndCancel(s"${incoherenceMessage(other.types.base)}. Found ${prettyType(other.types.show)} and ${prettyType(transmittable.types.show)}.", pos)
                  else if !(transmittable.types.proxy =:= other.types.proxy) then
                    errorAndCancel(s"${incoherenceMessage(other.types.base)}. Found ${prettyType(other.types.showMore)} and ${prettyType(transmittable.types.showMore)}.", pos)
                  else
                    errorAndCancel(s"${incoherenceMessage(other.types.base)} with type ${prettyType(transmittable.types.showMore)}.", pos)
            case _ =>
              accessorResolutionTypeMap.addNewTypeEntry(transmittable.types.base, AccessorResolution(transmittable = Some(transmittable), marshallable = None))
        else
          errorAndCancel(s"Illegal transmittable for type ${prettyType(transmittable.types.base.prettyShow)} referring to local variable.", pos)

    accessorResolutionTypeMap flatMapValuesInPlace:
      _.transmittable flatMap: transmittable =>
        Resolution.Result(transmittable.tree).asTransmittable(allowAbstractMarshallables).toOption map: transmittable =>
          AccessorResolution(transmittable = Some(transmittable), marshallable = None)

    val inheritedPlacedAccessors =
      synthesizeAllPlacedAccessors(module, includeFirst = false)

    SymbolMutator.getOrErrorAndAbort.invalidateMemberCaches(module)

    val inheritedValues =
      if !canceled then
        module.fieldMembers.iterator ++ module.methodMembers.iterator flatMap: member =>
          if member.owner != module &&
             !(member.flags is Flags.Synthetic) &&
             !(member.flags is Flags.Artifact) &&
             !(member.flags is Flags.Private) then
            val tpe = ThisType(module).memberType(member)
            PlacementInfo(tpe.resultType) flatMap: placementInfo =>
              if !placementInfo.modality.local then
                def hasPlacedAccessor =
                  Iterator(member) ++ member.allOverriddenSymbols exists { inheritedPlacedAccessors contains _ }

                def sameTypeInOwner =
                  val tpeInOwner = ThisType(member.owner).memberType(member)
                  PlacementInfo(tpeInOwner) forall: placementInfoInOwner =>
                    tpe.withResultType(placementInfo.valueType) =:= tpeInOwner.withResultType(placementInfoInOwner.valueType)

                Option.when(accessorGeneration == Forced || !hasPlacedAccessor || !sameTypeInOwner):
                  val info = if hasSyntheticMultitierContextArgument(member) then dropLastArgumentList(tpe) else tpe
                  (Some(member),
                   accessorSignature(signaturePrefix :+ TypeToken(targetName(member)), argumentTypes(info), placementInfo.valueType),
                   info.withResultType(placementInfo.valueType),
                   () => accessorGenerationFailureMessageProlog(symbolForName = Some(member), symbolForParent = Some(member), noninheritedPosition = None))
              else
                None
          else
            None
      else
        List.empty
    end inheritedValues

    val inheritedMarshallables = MutableCachedTypeSeqMap[mutable.SortedSet[Marshallable]]

    if !canceled then
      given Ordering[Marshallable] = (marshallable0, marshallable1) =>
        (marshallable0.signature, marshallable1.signature) match
          case (`abstractSignature`, signature1) if signature1 != abstractSignature => 1
          case (signature0, `abstractSignature`) if signature0 != abstractSignature => -1
          case (`unknownSignature`, signature1) if signature1 != unknownSignature => 1
          case (signature0, `unknownSignature`) if signature0 != unknownSignature => -1
          case (signature0, signature1) => signature0 compare signature1 match
            case 0 => marshallable0.symbol.name compare marshallable1.symbol.name
            case result => result

      val definedOrOverriddenMarshallables = mutable.Set.empty[String]

      module.typeRef.baseClasses.tail foreach: base =>
        if isMultitierModule(base) then
          val accessors = synthesizeAccessors(base)
          accessors.overridden.iterator ++ accessors.marshalling.iterator foreach: (symbol, _) =>
            if !(definedOrOverriddenMarshallables contains symbol.name) then
              definedOrOverriddenMarshallables += symbol.name
              Marshallable(symbol, module) foreach: marshallable =>
                inheritedMarshallables.lookupType(marshallable.types.base) match
                  case Some(marshallables) => marshallables += marshallable
                  case _ => inheritedMarshallables.addNewTypeEntry(marshallable.types.base, mutable.SortedSet(marshallable))
    end if

    val serializableTypeMap = MutableCachedTypeSeqMap[Term]

    def resolveSerializable(tpe: TypeRepr) =
      serializableTypeMap.lookupType(tpe) match
        case Some(term) =>
          Right(term)
        case _ =>
          val serializable = Resolution.resolveSerializable(tpe)
          serializable foreach { serializableTypeMap.addNewTypeEntry(tpe, _) }
          serializable

    def marshallableConstruction(transmittable: Transmittable) =
      if transmittable.signature != abstractSignature then
        def contextBuilders(tpe: TypeRepr): Either[String, Term] =
          tpe.typeArgs match
            case List(tail, head) =>
              val headTypes = TransmittableTypes(head)
              contextBuilder(headTypes) flatMap: builder =>
                contextBuilders(tail) map: builders =>
                  Ref(symbols.listContext).appliedToTypes(headTypes.typeList :+ tail).appliedTo(builder, builders)
            case _ =>
              val types = TransmittableTypes(tpe)
              contextBuilder(types) map:
                Ref(symbols.delegateContext).appliedToTypes(types.typeList).appliedTo(_)

        def contextBuilder(types: TransmittableTypes): Either[String, Term] =
          if types.transmittables derivesFrom symbols.delegates then
            val delegating = types.transmittables.baseType(symbols.delegates).typeArgs.head
            contextBuilders(delegating) map:
              Ref(symbols.delegatingContext).appliedToType(delegating).appliedTo(_)
          else if types.transmittables derivesFrom symbols.message then
            val transmittable = types.transmittables.baseType(symbols.message).typeArgs.head
            val transmittableTypes = TransmittableTypes(transmittable)
            contextBuilder(transmittableTypes) flatMap: builder =>
              resolveSerializable(transmittableTypes.intermediate) map: serializer =>
                Ref(symbols.messagingContext).appliedToTypes(transmittableTypes.typeList).appliedTo(builder, serializer)
          else if types.transmittables derivesFrom symbols.none then
            Right(Ref(symbols.noneContext))
          else
            Left(s"${prettyType(types.base.prettyShow)} is not transmittable")

        contextBuilder(transmittable.types) flatMap: builder =>
          resolveSerializable(transmittable.types.intermediate) map: serializer =>
            Some:
              Ref(symbols.marshallableResolution)
                .appliedToTypes(transmittable.types.typeList)
                .appliedTo(transmittable.tree, serializer, builder)
      else
        Right(None)
    end marshallableConstruction

    def marshallable(signature: String, types: MarshallableTypes, rhs: Option[Term], flags: Flags, generateName: () => String) =
      val typeSignatures = types.typeList.foldRight[Option[List[String]]](Some(List.empty)):
        case (tpe, Some(types)) => serializeTypeAndSanityCheck(tpe, module) map { (_, signature) => signature :: types }
        case _ => None

      if typeSignatures.nonEmpty || locallyScoped || signature != abstractSignature then
        val symbol = newVal(module, generateName(), symbols.marshallable.typeRef.appliedTo(types.typeList), flags | Flags.Lazy | Flags.Protected, Symbol.noSymbol)
        trySetThreadUnsafe(symbol)
        injectFieldSymbol(symbol)

        signature :: typeSignatures.toList.flatten match
          case List(signature, base, result, proxy) if !locallyScoped =>
            SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, marshallableInfo(signature, base, result, proxy))
          case _ =>

        val marshallable = Marshallable(symbol, types, signature)
        val definition = ValDef(symbol, Some(rhs.fold(Literal(NullConstant()).select(symbols.asInstanceOf).appliedToType(symbol.info)) { _.changeOwner(symbol) }))
        Right(marshallable, definition)
      else
        Left(s"Failed to serialize type for ${prettyType(TransmittableTypes(types.base, TypeBounds.empty, types.result, types.proxy, TypeBounds.empty).showMore)}.")
    end marshallable

    var marshallableIndex = 0

    enum RequiredMarshallable(val maybeResult: Option[TypeRepr], val maybeProxy: Option[TypeRepr]):
      val base: TypeRepr
      case Base(base: TypeRepr) extends RequiredMarshallable(None, None)
      case Result(base: TypeRepr, result: TypeRepr) extends RequiredMarshallable(Some(result), None)
      case Proxy(base: TypeRepr, result: TypeRepr, proxy: TypeRepr) extends RequiredMarshallable(Some(result), Some(proxy))

    def generateMarshallable(required: RequiredMarshallable, allowSkippingAbstract: Boolean, overridingName: Option[String]): Either[String, () => Either[String, Option[Marshallable]]] =
      val requiredTypes = TransmittableTypes(
        required.base,
        TypeBounds.empty,
        required.maybeResult getOrElse TypeBounds.empty,
        required.maybeProxy getOrElse TypeBounds.empty,
        TypeBounds.empty)

      def transmittableResolutionFailureMessage(types: TransmittableTypes) =
        val message = s"${prettyType(types.base.prettyShow)} is not transmittable"
        if required.maybeProxy.nonEmpty then s"$message. Found ${prettyType(types.showMore)}, required ${prettyType(requiredTypes.showMore)}."
        else s"$message. Found ${prettyType(types.show)}, required ${prettyType(requiredTypes.show)}."

      def generateMarshallableName() =
        overridingName getOrElse:
          val name = s"${names.marshalling}$mangledName$$$marshallableIndex"
          marshallableIndex += 1
          name

      def generateMarshallable(resolution: AccessorResolution, types: TransmittableTypes, signature: Option[String], rhs: () => Either[String, Option[Term]]) =
        val (transmittableTypes, transmittableSignature) = resolution.transmittable match
          case Some(Transmittable(_, types, signature)) => (types, Some(signature))
          case _ =>  (types, signature)

        info(s"  - Synthesizing marshallable for ${transmittableTypes.showMore}")

        val generatedMarshallable =
          resolution.marshallable match
            case Some(Some(marshallable, _)) =>
              if marshallable.signature == abstractSignature && resolution.allowSkippingAbstract then
                info("    Skipping synthesis of abstract Marshallable")
                Right(None)
              else
                info(s"    Selecting ${marshallable.types.show} [signature ${marshallable.signature}]")
                Right(Some(marshallable))
            case Some(_) =>
              info("    Skipping synthesis of abstract Marshallable")
              Right(None)
            case _ =>
              transmittableSignature match
                case Some(transmittableSignature) =>
                  if transmittableSignature != abstractSignature || !resolution.allowSkippingAbstract then
                    val flags = if overridingName.isDefined then Flags.Override else Flags.EmptyFlags
                    val body = if transmittableSignature != abstractSignature then rhs() else Right(None)
                    body flatMap: body =>
                      marshallable(transmittableSignature, transmittableTypes.asMarshallableTypes, body, flags, generateMarshallableName) map: (marshallable, definition) =>
                        info(s"    Selecting ${marshallable.types.show} [signature ${marshallable.signature}]")
                        resolution.marshallable = Some(Some(marshallable, Right(definition)))
                        Some(marshallable)
                  else
                    info("    Skipping synthesis of abstract Marshallable")
                    resolution.marshallable = Some(None)
                    Right(None)
                case _ =>
                  Left(transmittableResolutionFailureMessage(transmittableTypes))

        generatedMarshallable.left foreach: message =>
          info(s"    Synthesis failed: $message")

        generatedMarshallable
      end generateMarshallable

      def predefinedMarshallable(marshallable: Marshallable) =
        info(s"  - Selecting built-in ${marshallable.types.show}")
        Some(marshallable)

      def skipMarshallable() =
        info("  - Skipping synthesis of abstract Marshallable")
        None

      def accessorTransmittableInfo(resolution: AccessorResolution, types: MarshallableTypes) =
        resolution.transmittable match
          case Some(transmittable) =>
            (transmittable.types, Some(transmittable.signature))
          case _ =>
            (TransmittableTypes(types.base, TypeBounds.empty, types.result, types.proxy, TypeBounds.empty), None)

      extension (self: TypeRepr) def <:<?(other: TypeRepr) =
        typeParamMasker.mask(self) <:< typeParamMasker.mask(other)

      def conformsToRequiredMarshallable(types: MarshallableTypes) =
        required.base <:<? types.base &&
        (required.maybeResult forall { types.result <:<? _ }) &&
        (required.maybeProxy forall { types.proxy <:<? _ })

      def conformsToRequiredMarshallableWithGeneralizedResultType(types: MarshallableTypes) =
        required.base <:<? types.base &&
        (required.maybeResult forall { _ <:< types.result }) &&
        (required.maybeProxy forall { types.proxy <:<? _ })

      def conformsToPredefinedMarshallable(base: TypeRepr) =
        conformsToRequiredMarshallable(MarshallableTypes(base, base, symbols.future.typeRef.appliedTo(base)))

      def conformsToMarshallableTypes(types: MarshallableTypes, marshallableTypes: MarshallableTypes) =
        marshallableTypes.base <:<? types.base &&
        types.result <:<? marshallableTypes.result &&
        types.proxy <:<? marshallableTypes.proxy

      def checkTransmittableConformation(types: TransmittableTypes, transmittable: Option[Transmittable], resolution: Option[AccessorResolution]) =
        inline def generalizableToAbstract =
          (accessorGeneration == Deferred || accessorGeneration == Preferred || allowSkippingAbstract) &&
          conformsToRequiredMarshallableWithGeneralizedResultType(types.asMarshallableTypes) &&
          transmittable.isDefined

        if conformsToRequiredMarshallable(types.asMarshallableTypes) then
          Right(resolution)
        else if generalizableToAbstract then
          val transmittableTypes = types.copy(result = required.maybeResult getOrElse types.result)
          info(s"    Generalizing to ${transmittableTypes.showMore} [signature $abstractSignature] due to type mismatch")
          val accessor = resolution getOrElse accessorResolutionTypeMap.addNewTypeEntry(transmittableTypes.base, AccessorResolution())
          accessor.transmittable = Some(Transmittable(transmittable.get.tree, transmittableTypes, abstractSignature))
          accessor.marshallable = None
          Right(Some(accessor))
        else
          Left(transmittableResolutionFailureMessage(types))
      end checkTransmittableConformation

      def checkAccessorTransmittableTypesConformation[T](types: TransmittableTypes, resolution: AccessorResolution)(body: => Either[String, T]) =
        checkTransmittableConformation(types, resolution.transmittable, Some(resolution)) flatMap: _ =>
          body

      def checkAccessorTransmittableConformation[T](transmittable: Transmittable, resolution: Option[AccessorResolution])(body: (Option[AccessorResolution], Transmittable) => Either[String, T]) =
        checkTransmittableConformation(transmittable.types, Some(transmittable), resolution) flatMap: resolution =>
          body(resolution, resolution flatMap { _.transmittable } getOrElse transmittable)

      def lookupInheritedMarshallable(resolution: Option[AccessorResolution], transmittable: Option[Transmittable]) =
        inheritedMarshallables.lookupType(required.base) flatMap:
          _ collectFirst Function.unlift: marshallable =>
            val conforms =
              conformsToRequiredMarshallable(marshallable.types) &&
              (transmittable.isDefined ||
                allowAbstractMarshallables && overridingName.isEmpty ||
                marshallable.signature != abstractSignature) &&
              (transmittable orElse (resolution flatMap { _.transmittable }) forall: transmittable =>
                conformsToMarshallableTypes(marshallable.types, transmittable.types.asMarshallableTypes) &&
                (transmittable.signature == abstractSignature || marshallable.signature != abstractSignature) &&
                (accessorGeneration != Forced || marshallable.signature == transmittable.signature && marshallable.signature != unknownSignature))
            Option.when(conforms):
              info(s"    Selecting inherited ${marshallable.types.show} [signature ${marshallable.signature}]")
              val accessor = resolution getOrElse accessorResolutionTypeMap.addNewTypeEntry(required.base, AccessorResolution())
              val (types, signature) = accessorTransmittableInfo(accessor, marshallable.types)
              accessor.marshallable = Some(Some(marshallable, Left(marshallable.symbol)))
              accessor.allowSkippingAbstract &= allowSkippingAbstract
              () => generateMarshallable(accessor, types, signature, () => Right(None))

      info(s"  - Synthesizing marshallable for ${requiredTypes.showMore}")

      val resolution = accessorResolutionTypeMap.lookupType(required.base) map: resolution =>
        resolution -> AccessorResolution(resolution.transmittable, resolution.marshallable, resolution.allowSkippingAbstract)

      val generatedMarshallable =
        predefinedMarshallables find { marshallable => conformsToPredefinedMarshallable(marshallable.types.base) } match
          case Some(marshallable) =>
            info(s"    Selecting built-in ${marshallable.types.show}")
            Right(() => Right(predefinedMarshallable(marshallable)))
          case _ =>
            val forcedResolution =
              Option.when(accessorGeneration == Forced):
                accessorResolutionTypeMap.lookupType(required.base) match
                  case Some(resolution) =>
                    resolution.allowSkippingAbstract &= allowSkippingAbstract
                    resolution.marshallable match
                      case Some(Some(marshallable, Left(_))) if resolution.transmittable.isEmpty =>
                        info(s"    Revoking inherited ${marshallable.types.show} [signature ${marshallable.signature}] due to $Forced Mode")
                        resolution.marshallable = None
                      case _ =>
                    Right(resolution)
                  case _ =>
                    info("    Resolving Transmittable through implicit resolution")
                    val transmittable = Resolution.resolveTransmittable(required.base, allowAbstractMarshallables && overridingName.isEmpty)
                    if transmittable.isLeft then
                      info("    Resolution failed")
                    transmittable map: transmittable =>
                      info(s"    Resolved ${transmittable.types.showMore} [signature: ${transmittable.signature}]")
                      accessorResolutionTypeMap.addNewTypeEntry(transmittable.types.base, AccessorResolution(transmittable = Some(transmittable), marshallable = None, allowSkippingAbstract))

            val forcedResolutionFailure =
              forcedResolution flatMap { _.left.toOption }

            val fastResolution =
              forcedResolution flatMap { _.toOption } orElse accessorResolutionTypeMap.lookupType(required.base) match
                case Some(resolution) =>
                  resolution.allowSkippingAbstract &= allowSkippingAbstract
                  resolution.marshallable match
                    case Some(Some(marshallable, Left(_))) if !conformsToRequiredMarshallable(marshallable.types) =>
                      info(s"    Revoking inherited ${marshallable.types.show} [signature ${marshallable.signature}] due to type mismatch")
                      resolution.marshallable = None
                      Left(Some(resolution))
                    case Some(Some(marshallable, definition)) =>
                      if marshallable.signature == abstractSignature && allowSkippingAbstract then
                        info("    Skipping synthesis of previously selected abstract Marshallable")
                        Right(Right(() => Right(skipMarshallable())))
                      else if marshallable.signature == abstractSignature && overridingName.isDefined then
                        Left(Some(resolution))
                      else
                        val (types, signature) =
                          accessorTransmittableInfo(resolution, marshallable.types)
                        val generatedMarshallable =
                          checkAccessorTransmittableTypesConformation(types, resolution):
                            info(s"    Selecting ${if definition.isRight then "synthesized" else "inherited"} ${marshallable.types.show} [signature ${marshallable.signature}]")
                            Right(() => generateMarshallable(resolution, types, signature, () => Right(None)))
                        if generatedMarshallable.isLeft then
                          Right(lookupInheritedMarshallable(Some(resolution), None).fold(generatedMarshallable) { Right(_) })
                        else
                          Right(generatedMarshallable)
                    case Some(_) =>
                      if !allowSkippingAbstract then
                        info("    Revoking previously selected abstract Marshallable")
                        resolution.marshallable = None
                        Left(Some(resolution))
                      else
                        info("    Skipping synthesis of previously selected abstract Marshallable")
                        Right(Right(() => Right(skipMarshallable())))
                    case _ =>
                      Left(Some(resolution))
                case _ =>
                  Left(None)
            end fastResolution

            fastResolution match
              case Right(result) =>
                result
              case Left(resolution) =>
                resolution flatMap { resolution => resolution.transmittable map { resolution -> _ } } match
                  case Some(resolution, transmittable) =>
                    info(s"    Found existing ${transmittable.types.showMore} [signature: ${transmittable.signature}]")
                    checkAccessorTransmittableConformation(transmittable, Some(resolution)): (_, transmittable) =>
                      lookupInheritedMarshallable(Some(resolution), Some(transmittable)) map { Right(_) } getOrElse:
                        info(s"    Selecting ${transmittable.types.showMore} [signature: ${transmittable.signature}]")
                        Right(() => generateMarshallable(resolution, transmittable.types, Some(transmittable.signature), () => marshallableConstruction(transmittable)))

                  case _ =>
                    info("    Missing Transmittable")
                    val marshallable =
                      if accessorGeneration != Forced && forcedResolutionFailure.isEmpty then
                        lookupInheritedMarshallable(resolution, None) map { Right(_) }
                      else
                        None

                    marshallable getOrElse:
                      forcedResolutionFailure map { Left(_) } getOrElse:
                        info("    Resolving Transmittable through implicit resolution")
                        val transmittable = Resolution.resolveTransmittable(required.base, allowAbstractMarshallables && overridingName.isEmpty)
                        if transmittable.isLeft then
                          info("    Resolution failed")
                        transmittable flatMap: transmittable =>
                          info(s"    Resolved ${transmittable.types.showMore} [signature: ${transmittable.signature}]")
                          checkAccessorTransmittableConformation(transmittable, resolution): (resolution, transmittable) =>
                            lookupInheritedMarshallable(resolution, Some(transmittable)) map { Right(_) } getOrElse:
                              val accessor = resolution getOrElse accessorResolutionTypeMap.addNewTypeEntry(required.base, AccessorResolution())
                              accessor.transmittable = Some(transmittable)
                              accessor.marshallable = None
                              accessor.allowSkippingAbstract &= allowSkippingAbstract
                              info(s"    Selecting ${transmittable.types.showMore} [signature: ${transmittable.signature}]")
                              Right(() => generateMarshallable(accessor, transmittable.types, Some(transmittable.signature), () => marshallableConstruction(transmittable)))
      end generatedMarshallable

      generatedMarshallable.left foreach: message =>
        info(s"    Synthesis failed: $message")
        resolution foreach: (resolution, accessor) =>
          info("    Rolling back modifications of failed synthesis attempt")
          resolution.transmittable = accessor.transmittable
          resolution.marshallable = accessor.marshallable
          resolution.allowSkippingAbstract = accessor.allowSkippingAbstract

      generatedMarshallable
    end generateMarshallable

    def inheritedMarshallableResolutionFailureMessageProlog(marshallable: Symbol) =
      val name = marshallingIdentifier(marshallable.name)
      val symbol = inheritedPlacedAccessors.iterator collectFirst Function.unlift:
        case (_: Int, _) =>
          None
        case (symbol: Symbol @unchecked, placed) =>
          placedInfo(placed) flatMap: (_, arguments, result) =>
            Option.when(arguments == name || result == name) { symbol }
      accessorGenerationFailureMessageProlog(symbolForName = symbol, symbolForParent = Some(marshallable), noninheritedPosition = None)

    var placedIndex = 0
    var anonymousPlacedIndex = 0

    val allowSkippingAbstract = accessorGeneration == Deferred || accessorGeneration == Preferred

    inline def info(message: String) =
      println(s"[info] $message")

    if !canceled then
      info(s"Synthesizing remote accessors for ${fullName(module)} (Selection Phase, $accessorGeneration Mode)")

    var selectionPhaseEmpty = true

    val generatingMarshallables =
      values.reverseIterator ++ inheritedValues flatMap: (original, signature, tpe, position) =>
        if !canceled then
          val valueAccessed = original forall { accessed contains _ }
          val valuePrivate = original forall { _.flags is Flags.Private }

          selectionPhaseEmpty = false
          info(
            s"* ${(original filterNot { _.name startsWith names.block }).fold("Remote block") { symbol => s"Placed value ${symbol.name}" } } " +
            s"of type ${tpe.prettyShowFrom(module)} " +
            s"[${if valueAccessed then "accessed" else "not accessed"}] " +
            s"[${if valuePrivate then "private" else "not private"}] " +
            s"[$signature]")

          def argumentTypes(tpe: TypeRepr): List[TypeRepr] = tpe match
            case MethodType(_, paramTypes, resType) =>
              (paramTypes filter meaningfulArgumentType) ++ argumentTypes(resType)
            case PolyType(_, _, resType) =>
              argumentTypes(resType)
            case _ =>
              List.empty

          if valueAccessed || accessorGeneration != Deferred then
            val arguments = argumentTypes(tpe)
            val argumentType =
              if arguments.isEmpty then TypeRepr.of[Unit]
              else if arguments.sizeIs == 1 then arguments.head
              else Tuple(arguments)

            val resultType = tpe.resultType

            def marshallable(required: RequiredMarshallable) =
              generateMarshallable(required, (allowSkippingAbstract || valuePrivate) && !valueAccessed, overridingName = None)

            val marshallables =
              marshallable(RequiredMarshallable.Result(argumentType, argumentType)) flatMap: generateArgumentMarshallable =>
                marshallable(RequiredMarshallable.Base(resultType)) map: generateResultMarshallable =>
                  (generateArgumentMarshallable, generateResultMarshallable)

            marshallables match
              case Left(message) =>
                val (prolog, pos) = position()
                errorAndCancel(s"$prolog because $message", pos)
                None
              case Right(marshallables) =>
                Some((original, signature, tpe, position, valueAccessed, valuePrivate) ++ marshallables)
          else
            info("  Skipping synthesis for non-accessed placed value")
            None
        else
          None
    .toList
    end generatingMarshallables

    val implementingMarshallables =
      if accessorGeneration != Deferred then
        inheritedMarshallables.iterator flatMap:
          _.iterator flatMap:
            case Marshallable(symbol, types, `abstractSignature`) if !canceled =>
              selectionPhaseEmpty = false
              info(s"* Inherited abstract ${types.show}")
              val required = RequiredMarshallable.Proxy(types.base, types.result, types.proxy)
              generateMarshallable(required, allowSkippingAbstract = false, overridingName = Some(symbol.name)) match
                case Right(generateMarshallable) =>
                  Some(symbol, types, generateMarshallable)
                case Left(message) =>
                  if accessorGeneration == Required || accessorGeneration == Forced then
                    val (prolog, pos) = inheritedMarshallableResolutionFailureMessageProlog(symbol)
                    errorAndCancel(s"$prolog because $message", pos)
                  else
                    info("    Skipping synthesis for implementation of inherited abstract Marshallable")
                  None
            case _ =>
              None
      .toList
      else
        List.empty

    if !canceled && selectionPhaseEmpty then
      info("* None found")

    if !canceled then
      info(s"Synthesizing remote accessors for ${fullName(module)} (Generation Phase, $accessorGeneration Mode)")

    var generationPhaseEmpty = true

    val accessors = generatingMarshallables flatMap: (original, signature, tpe, position, valueAccessed, valuePrivate, generateArgumentMarshallable, generateResultMarshallable) =>
      if !canceled then
        generationPhaseEmpty = false
        info(
          s"* ${(original filterNot { _.name startsWith names.block }).fold("Remote block") { symbol => s"Placed value ${symbol.name}" } } " +
          s"of type ${tpe.prettyShowFrom(module)} " +
          s"[${if valueAccessed then "accessed" else "not accessed"}] " +
          s"[${if valuePrivate then "private" else "not private"}] " +
          s"[$signature]")

        val argumentMarshallable = generateArgumentMarshallable()
        val resultMarshallable = generateResultMarshallable()

        val marshallables =
          argumentMarshallable flatMap: argumentMarshallable =>
            resultMarshallable map: resultMarshallable =>
              argumentMarshallable flatMap: argumentMarshallable =>
                resultMarshallable map: resultMarshallable =>
                  (argumentMarshallable, resultMarshallable)

        marshallables match
          case Left(message) =>
            if valueAccessed || accessorGeneration != Preferred then
              val (prolog, pos) = position()
              errorAndCancel(s"$prolog because $message", pos)
            None

          case Right(None) =>
            None

          case Right(Some(argumentMarshallable, resultMarshallable)) =>
            val arguments = marshallingIdentifier(argumentMarshallable.symbol.name)
            val result = marshallingIdentifier(resultMarshallable.symbol.name)

            val inheritedPlacedWithIdenticalMarshallables =
              original exists: original =>
                Iterator(original) ++ original.allOverriddenSymbols collectFirst Function.unlift(inheritedPlacedAccessors.get) exists:
                  placedInfo(_) exists:
                    case (_, `arguments`, `result`) => true
                    case _ => false

            if inheritedPlacedWithIdenticalMarshallables then
              info("    Skipping synthesis because placed value is already associated to resolved Marshallable")

            Option.unless(inheritedPlacedWithIdenticalMarshallables):
              val name = s"${names.placed}$mangledName$$$placedIndex"
              placedIndex += 1

              val signatureConstruction =
                Ref(symbols.valueSignature).appliedTo(
                  Literal(StringConstant(signature)),
                  Ref(identifierSymbol),
                  Ref(signatureSymbol).select(symbols.valueSignaturePath))

              val info = symbols.placedValue.typeRef.appliedTo(
                List(
                  argumentMarshallable.types.base,
                  argumentMarshallable.types.result,
                  resultMarshallable.types.base,
                  resultMarshallable.types.proxy))
              val symbol = newVal(module, name, info, Flags.Final | Flags.Protected, Symbol.noSymbol)
              injectFieldSymbol(symbol)

              inline def reference(symbol: Symbol) =
                if symbol.owner.owner == types.marshallable.typeSymbol.companionModule.moduleClass then
                  Ref(symbol)
                else
                  This(module).select(symbol)

              val rhs = New(TypeIdent(symbols.placedValue)).select(symbols.placedValue.primaryConstructor).appliedToTypes(info.typeArgs).appliedTo(
                signatureConstruction,
                Literal(BooleanConstant(original exists { _.isStable })),
                reference(argumentMarshallable.symbol),
                reference(resultMarshallable.symbol))

              if !locallyScoped then
                SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, placedValueInfo(signature, arguments, result))

              val key = original getOrElse:
                val key = anonymousPlacedIndex
                anonymousPlacedIndex += 1
                key

              key -> (symbol, Some(ValDef(symbol, Some(rhs))))
      else
        None
    end accessors

    val overriding =
      implementingMarshallables flatMap: (symbol, types, generateMarshallable) =>
        if !canceled then
          selectionPhaseEmpty = false
          info(s"* Inherited abstract ${types.show}")
          generateMarshallable() match
            case Left(message) =>
              val (prolog, pos) = inheritedMarshallableResolutionFailureMessageProlog(symbol)
              errorAndCancel(s"$prolog because $message", pos)
              None
            case Right(None) =>
              val (prolog, pos) = inheritedMarshallableResolutionFailureMessageProlog(symbol)
              errorAndCancel(s"$prolog.", pos)
              None
            case Right(Some(resolvedMarshallable)) =>
              if resolvedMarshallable.symbol.name == symbol.name then
                info("    Skipping synthesis because selected Marshallable is the one to be implemented")
                None
              else
                val generatedMarshallable = marshallable(
                  resolvedMarshallable.signature,
                  resolvedMarshallable.types,
                  Some(This(module).select(resolvedMarshallable.symbol)),
                  Flags.Override,
                  () => symbol.name)
                generatedMarshallable match
                  case Left(message) =>
                    val (prolog, pos) = inheritedMarshallableResolutionFailureMessageProlog(symbol)
                    errorAndCancel(s"$prolog because $message", pos)
                    None
                  case Right(_, generatedMarshallable) =>
                    info("    Implementing inherited abstract Marshallable")
                    Some(generatedMarshallable.symbol -> Some(generatedMarshallable))
        else
          None
    end overriding

    if !canceled && generationPhaseEmpty then
      info("* None found")

    val marshalling =
      val marshallables = (overriding.iterator map { (symbol, _) => symbol }).toSet
      accessorResolutionTypeMap flatMapValues:
        _.marshallable.flatten flatMap: (_, marshallable) =>
          val symbol = (marshallable map { _.symbol }).merge
          Option.unless(marshallables contains symbol):
            (symbol, marshallable.toOption)

    val placed = accessors.to(SeqMap)

    SymbolMutator.getOrErrorAndAbort.resetFlag(module, Flags.NoInits)
    PureInterfaceFlag foreach: PureInterfaceFlag =>
      SymbolMutator.getOrErrorAndAbort.resetFlag(module, PureInterfaceFlag)

    Accessors(identifier, signature, peers, overriding, marshalling, placed)
  end synthesizeAccessorsFromTree

  private def synthesizeAccessorsFromClass(module: Symbol, moduleClass: Class[?]): Accessors =
    val signaturePrefix = accessorSignaturePrefix(module)

    val inheritedPlacedAccessors =
      synthesizeAllPlacedAccessors(module, includeFirst = false)

    SymbolMutator.getOrErrorAndAbort.invalidateMemberCaches(module)

    val marshalling = MutableCachedTypeSeqMap[(Symbol, Option[ValDef])]
    val overridden = mutable.ListBuffer.empty[(Symbol, Option[ValDef])]
    val placed = mutable.ListBuffer.empty[(Symbol | Int, (Symbol, Option[ValDef]))]

    val declaredMethods =
      try
        moduleClass.getDeclaredMethods
      catch case NonFatal(_) =>
        errorAndCancel(
          s"Failed to access list of methods declared in ${prettyType(fullName(module))}.",
          Position.ofMacroExpansion.firstCodeLine)
        Array.empty[Method]

    val inheritedValues =
      inheritedPlacedAccessors.iterator flatMap:
        case (_: Int, _) => None
        case (symbol: Symbol @unchecked, placed) => placedInfo(placed) map { (signature, _, _) => signature -> symbol }

    val declaredValues =
      module.fieldMembers.iterator ++ module.methodMembers.iterator flatMap: member =>
        if !(member.flags is Flags.Synthetic) && !(member.flags is Flags.Artifact) then
          val tpe = ThisType(module).memberType(member)
          PlacementInfo(tpe.resultType) flatMap: placementInfo =>
            Option.unless(placementInfo.modality.local):
              val info = if hasSyntheticMultitierContextArgument(member) then dropLastArgumentList(tpe) else tpe
              accessorSignature(signaturePrefix :+ TypeToken(targetName(member)), argumentTypes(info), placementInfo.valueType) -> member
        else
          None

    val values = (inheritedValues ++ declaredValues).toMap

    declaredMethods foreach: method =>
      if (method.getName startsWith names.marshalling) &&
         !module.declaredField(method.getName).exists &&
         method.getParameterCount == 0 &&
         method.getReturnType == classes.marshallable then
        val marshallable = method.getAnnotation(classes.marshallableInfo)
        if marshallable != null then
          val types =
            TypeToken.deserializeType(marshallable.base, module) flatMap: base =>
              TypeToken.deserializeType(marshallable.result, module) flatMap: result =>
                TypeToken.deserializeType(marshallable.proxy, module) map: proxy =>
                  (base, result, proxy)

          if types.isEmpty then
            val message = s"Failed to deserialize types for remote accessor in ${prettyType(fullName(module))}: $marshallable"
            val pos = Position.ofMacroExpansion.firstCodeLine
            if marshallable.signature == abstractSignature then
              errorAndCancel(message, pos)
            else
              report.warning(message, pos)

          types foreach: (base, result, proxy) =>
            val overriding = module.typeRef.baseClasses.tail exists { _.declaredField(method.getName).exists }
            val annotation = marshallableInfo(marshallable.signature, marshallable.base, marshallable.result, marshallable.proxy)
            val info = symbols.marshallable.typeRef.appliedTo(List(base, result, proxy))
            val flags = if overriding then Flags.Override else Flags.EmptyFlags
            val symbol = newVal(module, method.getName, info, Flags.Lazy | Flags.Protected, Symbol.noSymbol)
            SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, annotation)
            trySetThreadUnsafe(symbol)
            injectFieldSymbol(symbol)
            if overriding then
              overridden += symbol -> None
            else
              marshalling.addNewTypeEntry(base, symbol -> None)

    declaredMethods foreach: method =>
      if (method.getName startsWith names.placed) &&
         !module.declaredField(method.getName).exists &&
         method.getParameterCount == 0 &&
         method.getReturnType == classes.placedValue then
        val placedValue = method.getAnnotation(classes.placedValueInfo)
        if placedValue != null && !placedBlockSignature.matches(placedValue.signature) then
          val value = values.get(placedValue.signature)

          def resolveMarshallable(identifier: String) =
            val name = marshallingName(identifier)
            predefinedMarshallables find { _.symbol.name == name } orElse Marshallable(module.fieldMember(name), module)

          val valueMarshallables =
            value flatMap: value =>
              resolveMarshallable(placedValue.arguments) flatMap: arguments =>
                resolveMarshallable(placedValue.result) map: result =>
                  (value, arguments, result)

          val resolutionFailure =
            if value.isEmpty then "placed value"
            else if valueMarshallables.isEmpty then "marshallable types"
            else ""

          if resolutionFailure.nonEmpty then
            val message = s"Failed to resolve $resolutionFailure for remote accessor in ${prettyType(fullName(module))}: $placedValue"
            val pos = Position.ofMacroExpansion.firstCodeLine
            report.warning(message, pos)

          valueMarshallables foreach: (value, arguments, result) =>
            val annotation = placedValueInfo(placedValue.signature, placedValue.arguments, placedValue.result)
            val info = symbols.placedValue.typeRef.appliedTo(List(arguments.types.base, arguments.types.result, result.types.base, result.types.proxy))
            val symbol = newVal(module, method.getName, info, Flags.Final | Flags.Protected, Symbol.noSymbol)
            SymbolMutator.getOrErrorAndAbort.updateAnnotationWithTree(symbol, annotation)
            injectFieldSymbol(symbol)
            placed += value -> (symbol, None)

    val (identifier, signature, peers) = signatures(module)

    Accessors(identifier, signature, peers, overridden.result(), marshalling, placed.to(SeqMap))
  end synthesizeAccessorsFromClass
end RemoteAccessorSynthesis
