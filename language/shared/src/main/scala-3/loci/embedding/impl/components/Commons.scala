package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.{compileTimeOnly, experimental}
import scala.collection.mutable
import scala.reflect.TypeTest
import scala.quoted.{Expr, Quotes, quotes, Type}

object Commons:
  @compileTimeOnly("Construct cannot be used at run time.")
  transparent inline private def ?[T]: T =
    throw new NotImplementedError

  extension (expr: Expr[?])(using Quotes) private def symbol =
    import quotes.reflect.*
    expr.asTerm.underlyingArgument.symbol
end Commons

@experimental
trait Commons:
  this: Component =>
  import quotes.reflect.*

  import Commons.*

  object symbols:
    val `language.Local` = Symbol.requiredPackage("loci.language").typeMember("Local")
    val `language.per` = Symbol.requiredPackage("loci.language").typeMember("per")
    val `language.on` = Symbol.requiredPackage("loci.language").typeMember("on")
    val `embedding.on` = Symbol.requiredPackage("loci.embedding").typeMember("on")
    val `embedding.of` = Symbol.requiredPackage("loci.embedding").typeMember("of")
    val `embedding.placed` = Symbol.requiredPackage("loci.embedding").typeMember("placed")
    val from = Symbol.requiredPackage("loci.embedding").typeMember("from")
    val fromSingle = Symbol.requiredPackage("loci.embedding").typeMember("fromSingle")
    val fromMultiple = Symbol.requiredPackage("loci.embedding").typeMember("fromMultiple")
    val nonplaced = Symbol.requiredModule("loci.embedding.Multitier").typeMember("nonplaced")
    val nonplacedType = Symbol.requiredModule("loci.embedding.Multitier").typeMember("type")
    val base = TypeRepr.of[transmitter.Transmittable.Any[?, ?, ?]].typeSymbol.typeMember("Base")
    val intermediate = TypeRepr.of[transmitter.Transmittable.Any[?, ?, ?]].typeSymbol.typeMember("Intermediate")
    val result = TypeRepr.of[transmitter.Transmittable.Any[?, ?, ?]].typeSymbol.typeMember("Result")
    val proxy = TypeRepr.of[transmitter.Transmittable.Any[?, ?, ?]].typeSymbol.typeMember("Proxy")
    val transmittables = TypeRepr.of[transmitter.Transmittable.Any[?, ?, ?]].typeSymbol.typeMember("Transmittables")
    val `type` = TypeRepr.of[transmitter.Transmittable.Resolution[?, ?, ?, ?, ?]].typeSymbol.typeMember("Type")
    val `language.multitier` = TypeRepr.of[language.multitier].typeSymbol
    val `embedding.multitier` = TypeRepr.of[embedding.multitier].typeSymbol
    val on = TypeRepr.of[embedding.On[?]].typeSymbol
    val select = TypeRepr.of[embedding.Select[?]].typeSymbol
    val run = TypeRepr.of[embedding.Run[?, ?]].typeSymbol
    val capture = TypeRepr.of[embedding.Capture[?, ?, ?]].typeSymbol
    val block = TypeRepr.of[embedding.Block[?, ?, ?]].typeSymbol
    val narrow = TypeRepr.of[embedding.Narrow].typeSymbol
    val call = TypeRepr.of[embedding.Call[?, ?]].typeSymbol
    val placed = TypeRepr.of[Placed[?, ?]].typeSymbol
    val subjective = TypeRepr.of[Placed.Subjective[?, ?]].typeSymbol
    val remote = TypeRepr.of[language.Remote[?]].typeSymbol
    val remoteApply = '{ language.remote.apply }.symbol
    val selectApplySingle = '{ ?[embedding.Select[?]].apply(?[language.Remote[?]]) }.symbol
    val selectApplyMultiple = '{ ?[embedding.Select[?]].apply(?[language.Remote[?]], ?[language.Remote[?]]) }.symbol
    val selectApplySeq = '{ ?[embedding.Select[?]].apply(?[Seq[language.Remote[?]]]) }.symbol
    val callApply = '{ ?[embedding.Call[?, ?]].call(?) }.symbol
    val remoteReference = '{ language.Remote.reference(?) }.symbol
    val and = '{ language.and(?)(?)(using ?, ?) }.symbol
    val peer = TypeRepr.of[language.peer].typeSymbol
    val single = TypeRepr.of[language.Single[?]].typeSymbol
    val optional = TypeRepr.of[language.Optional[?]].typeSymbol
    val multiple = TypeRepr.of[language.Multiple[?]].typeSymbol
    val context = TypeRepr.of[Placement.Context.type].typeSymbol
    val multitierContext = TypeRepr.of[embedding.Multitier.Context.type].typeSymbol
    val subjectivity = TypeRepr.of[Subjectivity.type].typeSymbol
    val multiplicity = TypeRepr.of[Multiplicity.type].typeSymbol
    val tie = TypeRepr.of[Tie.type].typeSymbol
    val lowestCommonSuperType = TypeRepr.of[LowestCommonSuperType[?, ?, ?]].typeSymbol
    val delegates = TypeRepr.of[transmitter.Transmittables.Delegates[?]].typeSymbol
    val message = TypeRepr.of[transmitter.Transmittables.Message[?]].typeSymbol
    val none = TypeRepr.of[transmitter.Transmittables.None].typeSymbol
    val delegatingContext = '{ transmitter.ContextBuilder.delegating(using ?) }.symbol
    val messagingContext = '{ transmitter.ContextBuilder.messaging(using ?, ?) }.symbol
    val noneContext = '{ transmitter.ContextBuilder.none }.symbol
    val delegateContext = '{ transmitter.ContextBuilders.delegate(using ?) }.symbol
    val listContext = '{ transmitter.ContextBuilders.list(using ?, ?) }.symbol
    val transmittable = TypeRepr.of[transmitter.Transmittable.Resolution[?, ?, ?, ?, ?]].typeSymbol
    val serializable = TypeRepr.of[serializer.Serializable[?]].typeSymbol
    val marshallable = TypeRepr.of[transmitter.Marshallable[?, ?, ?]].typeSymbol
    val marshallableResolution = '{ transmitter.Marshallable.marshallable(?, ?, ?) }.symbol
    val marshallableUnit = '{ transmitter.Marshallable.unit }.symbol
    val marshallableNull = '{ transmitter.Marshallable.`null` }.symbol
    val marshallableNothing = '{ transmitter.Marshallable.nothing }.symbol
    val marshal = '{ ?[transmitter.Marshallable[?, ?, ?]].marshal(?, ?) }.symbol
    val unmarshal = '{ ?[transmitter.Marshallable[?, ?, ?]].unmarshal(?[MessageBuffer], ?) }.symbol
    val transmission = TypeRepr.of[language.transmitter.Transmission.type].typeSymbol
    val placedValue = TypeRepr.of[runtime.PlacedValue[?, ?, ?, ?]].typeSymbol
    val placedValueSignature = '{ ?[runtime.PlacedValue[?, ?, ?, ?]].signature }.symbol
    val placedValueArguments = '{ ?[runtime.PlacedValue[?, ?, ?, ?]].arguments }.symbol
    val placedValueResult = '{ ?[runtime.PlacedValue[?, ?, ?, ?]].result }.symbol
    val valueSignatureName = '{ ?[runtime.Value.Signature].name }.symbol
    val valueSignatureModule = '{ ?[runtime.Value.Signature].module }.symbol
    val valueSignaturePath = '{ ?[runtime.Value.Signature].path }.symbol
    val valueSignature = '{ runtime.Value.Signature.apply(?, ?, ?) }.symbol
    val peerSignature = '{ runtime.Peer.Signature.apply(?, ?, ?) }.symbol
    val peerSignatureCompare = '{ ?[runtime.Peer.Signature] <= ? }.symbol
    val peerTieSingle = '{ runtime.Peer.Tie.Single }.symbol
    val peerTieOptional = '{ runtime.Peer.Tie.Optional }.symbol
    val peerTieMultiple = '{ runtime.Peer.Tie.Multiple }.symbol
    val moduleSignature = '{ runtime.Module.Signature.apply(?[String]) }.symbol
    val moduleSignatureNested = '{ runtime.Module.Signature.apply(?[runtime.Module.Signature], ?[String]) }.symbol
    val valueReferenceRemote = '{ ?[runtime.Value.Reference].remote }.symbol
    val remoteReferenceSignature = '{ ?[runtime.Remote.Reference].signature }.symbol
    val invokeRemoteAccess = '{ ?[runtime.System].invokeRemoteAccess(?, ?, ?, ?, ?) }.symbol
    val subjectiveValue = '{ ?[runtime.System].subjectiveValue(?, ?) }.symbol
    val remoteValue = '{ runtime.RemoteValue.apply() }.symbol
    val remoteRequest = TypeRepr.of[runtime.RemoteRequest].typeSymbol
    val marshallableInfo = TypeRepr.of[runtime.MarshallableInfo].typeSymbol
    val placedValueInfo = TypeRepr.of[runtime.PlacedValueInfo].typeSymbol
    val erased = '{ embedding.erased }.symbol
    val erasedArgs = '{ embedding.erased(?) }.symbol
    val function1 = TypeRepr.of[Function1[?, ?]].typeSymbol
    val function1Apply = '{ ?[Function1[?, ?]].apply(?) }.symbol
    val contextFunction1 = TypeRepr.of[ContextFunction1[?, ?]].typeSymbol
    val contextFunction1Apply = '{ ?[ContextFunction1[?, ?]].apply(using ?) }.symbol
    val iterableMap = '{ ?[Iterable[?]].map(?) }.symbol
    val iterableIsEmpty = '{ ?[Iterable[?]].isEmpty }.symbol
    val iterableNonEmpty = '{ ?[Iterable[?]].nonEmpty }.symbol
    val listHead = '{ ?[List[?]].head }.symbol
    val listTail = '{ ?[List[?]].tail }.symbol
    val tryMap = '{ ?[util.Try[?]].map(?) }.symbol
    val tryFlatten = '{ ?[util.Try[?]].flatten(using ?) }.symbol
    val seq = TypeRepr.of[Seq[?]].typeSymbol
    val list = TypeRepr.of[List[?]].typeSymbol
    val map = TypeRepr.of[Map[?, ?]].typeSymbol
    val `try` = TypeRepr.of[util.Try[?]].typeSymbol
    val future = TypeRepr.of[concurrent.Future[?]].typeSymbol
    val contextResultCount = TypeRepr.of[annotation.internal.ContextResultCount].typeSymbol
    val threadUnsafe = TypeRepr.of[annotation.threadUnsafe].typeSymbol
    val compileTimeOnly = TypeRepr.of[annotation.compileTimeOnly].typeSymbol
    val targetName = TypeRepr.of[annotation.targetName].typeSymbol
    val asInstanceOf = '{ ?.asInstanceOf }.symbol
    val repeated = TypeRepr.of[`<repeated>`[?]].typeSymbol

  object types:
    val `language.on` = symbols.`language.on`.typeRef.appliedTo(List(TypeBounds.empty, TypeBounds.empty))
    val `embedding.on` = symbols.`embedding.on`.typeRef.appliedTo(List(TypeBounds.empty, TypeBounds.empty))
    val from = symbols.from.typeRef.appliedTo(List(TypeBounds.empty, TypeBounds.empty))
    val fromSingle = symbols.fromSingle.typeRef.appliedTo(List(TypeBounds.empty, TypeBounds.empty))
    val fromMultiple = symbols.fromMultiple.typeRef.appliedTo(List(TypeBounds.empty, TypeBounds.empty))
    val nonplaced = TypeRepr.of[embedding.Multitier.nonplaced]
    val nonplacedType = TypeRepr.of[embedding.Multitier.`type`[embedding.Multitier.nonplaced, ?]]
    val single = TypeRepr.of[Tie.Single]
    val optional = TypeRepr.of[Tie.Optional]
    val multiple = TypeRepr.of[Tie.Multiple]
    val messageBuffer = TypeRepr.of[MessageBuffer]
    val placedValue = TypeRepr.of[PlacedValue[?, ?]]
    val placed = TypeRepr.of[Placed[?, ?]]
    val subjective = TypeRepr.of[Placed.Subjective[?, ?]]
    val remote = TypeRepr.of[language.Remote[?]]
    val context = TypeRepr.of[Placement.Context[?]]
    val multitierContext = TypeRepr.of[embedding.Multitier.Context]
    val placedContext = TypeRepr.of[embedding.On.Placed.Context]
    val remoteRef = TypeRepr.of[transmitter.RemoteRef]
    val transmittable = TypeRepr.of[transmitter.Transmittable.Resolution[?, ?, ?, ?, ?]]
    val marshallable = TypeRepr.of[transmitter.Marshallable[?, ?, ?]]
    val transmission = TypeRepr.of[language.transmitter.Transmission[?, ?, ?, ?, ?]]
    val placedValues = TypeRepr.of[runtime.PlacedValues]
    val valueSignature = TypeRepr.of[runtime.Value.Signature]
    val valueReference = TypeRepr.of[runtime.Value.Reference]
    val peerSignature = TypeRepr.of[runtime.Peer.Signature]
    val peerTie = TypeRepr.of[runtime.Peer.Tie]
    val moduleSignature = TypeRepr.of[runtime.Module.Signature]
    val system = TypeRepr.of[runtime.System]
    val conversion = TypeRepr.of[Conversion[?, ?]]
    val seq = TypeRepr.of[Seq[?]]

  object names:
    val apply = "apply"
    val tie = "Tie"
    val from = "from"
    val to = "to"
    val anon = "$anon"
    val loci = "$loci$"
    val system = s"${loci}sys"
    val systemCreate = s"${loci}sys$$create"
    val dispatch = s"${loci}dispatch"
    val module = s"${loci}mod"
    val signature = s"${loci}sig"
    val peerSignature = s"${loci}peer$$sig$$"
    val peerTies = s"${loci}peer$$ties$$"
    val block = s"${loci}anon$$"
    val placed = s"${loci}placed$$"
    val marshalling = s"${loci}marshalling$$"
    val resolutionFailure = "resolutionFailure"

  object Tuple extends TupleExtractor(quotes)

  object MaybeTyped:
    def unapply(term: Term): Some[Term] = term match
      case Typed(MaybeTyped(expr), _) => Some(expr)
      case _ => Some(term)

  object MaybeInlined:
    def unapply(term: Term): Some[Term] = term match
      case Inlined(None, List(), MaybeInlined(body)) => Some(body)
      case _ => Some(term)

  object VarArgs:
    def unapply(terms: List[Term]): Some[List[Term]] = Some:
      terms flatMap:
        case Typed(Repeated(args, _), _)  => args
        case arg => List(arg)

  final class PackedValueType[T](using t: Type[T]):
    opaque type Type = T
    given quoted.Type[Type] = t

//  final class PackedValueType[T](using t: Type[T]):
//    opaque type Type1 = T
//    opaque type Type2 = T
//    opaque type Type3 = T
//    opaque type Type4 = T
//    given Type[Type1] = t
//    given Type[Type2] = t
//    given Type[Type3] = t
//    given Type[Type4] = t

  extension (tpe: TypeRepr)
    def asPackedValueType: PackedValueType[?] = tpe.asType match
      case t: Type[Any] @unchecked if tpe <:< TypeRepr.of[Any] => PackedValueType(using t)
      case _ => throw IllegalArgumentException(s"${tpe.safeShow} cannot be used as a value type")
    def prettyShow =
      tpe.safeShow(Printer.CompilerStyleTypeReprCode)
    def prettyShowFrom(symbol: Symbol) =
      tpe.safeShowFrom(symbol, Printer.CompilerStyleTypeReprCode)
    def safeShowFrom(symbol: Symbol): String =
      tpe.safeShowFrom(symbol, "<?>", quotes.reflect.Printer.SafeTypeReprCode)
    def safeShowFrom(symbol: Symbol, fallback: String): String =
      tpe.safeShowFrom(symbol, fallback, quotes.reflect.Printer.SafeTypeReprCode)
    def safeShowFrom(symbol: Symbol, printer: Printer[TypeRepr]): String =
      tpe.safeShowFrom(symbol, "<?>", printer)
    def safeShowFrom(symbol: Symbol, fallback: String, printer: Printer[TypeRepr]): String =
      val prefixes = mutable.Set.empty[String]
      object prefixesCollector extends TypeMap(quotes):
        override def transform(tpe: TypeRepr) = tpe match
          case TypeRef(qualifier @ ThisType(tref), _) if qualifier.typeSymbol == symbol || qualifier.typeSymbol == symbol.moduleClass =>
            prefixes +=
              s"${tref.safeShow("", printer)}." +=
              s"${tref.safeShow("", Printer.CompilerStyleTypeReprCode)}." +=
              s"${tref.safeShow("", Printer.TypeReprCode)}." +=
              s"${tref.safeShow("", Printer.TypeReprAnsiCode)}."
            super.transform(tpe)
          case _ =>
            super.transform(tpe)
      prefixesCollector.transform(tpe)
      def stripPrefix(result: String, prefix: String, index: Int): String =
        result.indexOf(prefix, index) match
          case _ if prefix.isEmpty =>
            result
          case -1 =>
            result
          case 0 =>
            stripPrefix(result.substring(prefix.length), prefix, 0)
          case index =>
            if Character.isWhitespace(result(index - 1)) ||
               result(index - 1) == ',' || result(index - 1) == ';' ||
               result(index - 1) == '(' || result(index - 1) == ')' ||
               result(index - 1) == '[' || result(index - 1) == ']' ||
               result(index - 1) == '{' || result(index - 1) == '}' then
              stripPrefix(s"${result.substring(0, index)}${result.substring(index + prefix.length)}", prefix, index)
            else
              stripPrefix(result, prefix, index + 1)
      prefixes.foldLeft(tpe.safeShow(fallback, printer)) { stripPrefix(_, _, 0) }

  extension (pos: Position)
    def firstCodeLine =
      if pos.startLine != pos.endLine then
        Position(pos.sourceFile, pos.start, SourceCode(pos.sourceFile).forwardSkipToLastTokenInLine(pos.start) + 1)
      else
        pos
    def lastCodeLine =
      if pos.startLine != pos.endLine then
        Position(pos.sourceFile, SourceCode(pos.sourceFile).backwardSkipToLastTokenInLine(pos.end - 1), pos.end)
      else
        pos

  extension (term: Term)
    def adaptedTo(tree: Tree) =
      val block = Block.copy(tree)(List(), term)
      term match
        case Wildcard() => Wildcard()
        case Ident(name) => Ident.copy(block)(name)
        case Select(qualifier, name) => Select.copy(block)(qualifier, name)
        case Literal(constant) => Literal.copy(block)(constant)
        case This(identifier) => This.copy(block)(identifier)
        case New(tpt) => New.copy(block)(tpt)
        case NamedArg(name, value) => NamedArg.copy(block)(name, value)
        case Apply(fun, args) => Apply.copy(block)(fun, args)
        case TypeApply(fun, args) => TypeApply.copy(block)(fun, args)
        case Super(qualifier, identifier) => Super.copy(block)(qualifier, identifier)
        case Assign(lhs, rhs) => Assign.copy(block)(lhs, rhs)
        case Block(statements, expr) => Block.copy(block)(statements, expr)
        case Closure(method, tpe) => Closure.copy(block)(method, tpe)
        case If(condition, thenBranch, elseBranch) => If.copy(block)(condition, thenBranch, elseBranch)
        case Match(scrutinee, cases) => Match.copy(block)(scrutinee, cases)
        case SummonFrom(cases) => SummonFrom.copy(block)(cases)
        case Try(body, cases, finalizer) => Try.copy(block)(body, cases, finalizer)
        case Return(expr, from) => Return.copy(block)(expr, from)
        case Repeated(elements, tpt) => Repeated.copy(block)(elements, tpt)
        case Inlined(call, bindings, body) => Inlined.copy(block)(call, bindings, body)
        case SelectOuter(qualifier, name, level) => SelectOuter.copy(block)(qualifier, name, level)
        case While(condition, body) => While.copy(block)(condition, body)
        case Typed(expr, tpt) => Typed.copy(block)(expr, tpt)
        case _ => term

  extension (symbol: Symbol)
    def findAncestor(predicate: Symbol => Boolean): Option[Symbol] =
      if symbol.exists then
        if predicate(symbol) then Some(symbol) else symbol.maybeOwner.findAncestor(predicate)
      else
        None
    def hasAncestor(predicate: Symbol => Boolean): Boolean =
      findAncestor(predicate).isDefined
    def hasAncestor(ancestors: Symbol*): Boolean =
      symbol hasAncestor { ancestors contains _ }
    def orElse(other: Symbol): Symbol =
      if symbol.exists then symbol else other
    def fold[T](ifEmpty: => T)(f: Symbol => T): T =
      if symbol.exists then f(symbol) else ifEmpty

  def newMethod(parent: Symbol, name: String, tpe: TypeRepr, flags: Flags, privateWithin: Symbol) =
    val symbol = Symbol.newMethod(parent, name, tpe, Flags.EmptyFlags, privateWithin)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol, flags.cleaned)
    symbol

  def newVal(parent: Symbol, name: String, tpe: TypeRepr, flags: Flags, privateWithin: Symbol) =
    val symbol = Symbol.newVal(parent, name, tpe, Flags.EmptyFlags, privateWithin)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol, flags.cleaned)
    symbol

  def newBind(parent: Symbol, name: String, flags: Flags, tpe: TypeRepr) =
    val symbol = Symbol.newBind(parent, name, Flags.EmptyFlags, tpe)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol,  flags.cleaned)
    symbol

  def newClass(parent: Symbol, name: String, flags: Flags, parents: List[TypeRepr], decls: Symbol => List[Symbol], selfType: Option[TypeRepr]) =
    val symbol = Symbol.newClass(parent, name, parents, decls, selfType)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol, flags.cleaned)
    symbol

  def newModule(parent: Symbol, name: String, modFlags: Flags, clsFlags: Flags, parents: List[TypeRepr], decls: Symbol => List[Symbol], privateWithin: Symbol) =
    val symbol = Symbol.newModule(parent, name, Flags.EmptyFlags, Flags.EmptyFlags, parents, decls, privateWithin)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol, modFlags.cleaned)
    SymbolMutator.getOrErrorAndAbort.setFlag(symbol.moduleClass, clsFlags.cleaned)
    symbol

  def contextMethodType[T: Type, R: Type] =
    val Inlined(_, _, Block(List(lambda), _)) = '{ (_: T) ?=> ?[R] }.asTerm: @unchecked
    val tpe @ MethodType(_, _, _) = lambda.symbol.info: @unchecked
    tpe

  def multitierModuleArgument(symbol: Symbol): Option[Term] =
    (symbol.getAnnotation(symbols.`language.multitier`) collect { case Apply(Apply(_, List(arg)), List(_)) => arg }) orElse
    (symbol.getAnnotation(symbols.`embedding.multitier`) collect { case Apply(_, List(arg)) => arg })

  def isMultitierModule(symbol: Symbol): Boolean =
    symbol.exists && (symbol.isField || symbol.isModuleDef || symbol.isClassDef) && !symbol.isPackageDef &&
    (symbol.info.baseClasses exists: symbol =>
      symbol.hasAnnotation(symbols.`language.multitier`) || symbol.hasAnnotation(symbols.`embedding.multitier`))

  def isMultitierNestedPath(symbol: Symbol): Boolean =
    symbol.exists && (isMultitierModule(symbol) || symbol.isModuleDef && isMultitierNestedPath(symbol.maybeOwner))

  def hasSyntheticMultitierContextArgument(symbol: Symbol): Boolean =
    symbol.paramSymss match
      case _ :+ List(param) =>
        isMultitierModule(symbol.maybeOwner) &&
        param.isTerm &&
        (param.flags is Flags.Synthetic) &&
        !(param.info =:= TypeRepr.of[Nothing]) &&
        param.info <:< types.multitierContext
      case _ =>
        false

  def dropLastArgumentList(tpe: TypeRepr): TypeRepr =
    inline def typeBounds(tpe: TypeRepr) = tpe match
      case tpe: TypeBounds => tpe
      case _ => TypeBounds(tpe, tpe)

    def dropLastArgumentList(tpe: MethodOrPoly): TypeRepr = tpe match
      case MethodType(paramNames, paramTypes, resultType: MethodOrPoly) =>
        MethodType(paramNames)(
          binder => paramTypes map { _.substituteParamRefs(tpe, binder) },
          dropLastArgumentList(resultType).substituteParamRefs(tpe, _))
      case PolyType(paramNames, paramBounds, resultType: MethodOrPoly) =>
        PolyType(paramNames)(
          binder => paramBounds map { param => typeBounds(param.substituteParamRefs(tpe, binder)) },
          dropLastArgumentList(resultType).substituteParamRefs(tpe, _))
      case MethodType(_, _, resultType) =>
        resultType

    tpe match
      case tpe: MethodOrPoly => dropLastArgumentList(tpe) match
        case tpe: MethodOrPoly => tpe
        case tpe => ByNameType(tpe)
      case _ => tpe
  end dropLastArgumentList

  def isStablePath(term: Term): Boolean = term match
    case This(_) | Super(_, _) | Ident(_) => true
    case Select(qualifier, _) => term.symbol.isStable && isStablePath(qualifier)
    case _ => false

  def clearTypeApplications(term: Term): Term = term match
    case Apply(fun, args) =>
      Apply.copy(term)(clearTypeApplications(fun), args)
    case TypeApply(fun, args) => fun.tpe.widenTermRefByName match
      case tpe @ PolyType(_, paramTypes, _) if paramTypes.sizeIs == args.size =>
        TypeApply.copy(term)(clearTypeApplications(fun), (paramTypes.indices map { i => TypeTree.of(using tpe.param(i).asType) }).toList)
      case _ =>
        TypeApply.copy(term)(clearTypeApplications(fun), args)
    case _ =>
      term

  def termAsSelection(term: Term, owner: Symbol): Option[Select] = term match
    case term @ Select(_, _) =>
      Some(term)
    case term @ Ident(_) if term.symbol.owner != defn.RootClass && !term.symbol.owner.isPackageDef =>
      if term.symbol.owner.isClassDef && term.symbol.owner.isModuleDef then
        Some(Ref(term.symbol.owner.companionModule).select(term.symbol))
      else if term.symbol.owner.isClassDef && (owner hasAncestor term.symbol.owner) then
        Some(This(term.symbol.owner).select(term.symbol))
      else
        None
    case _ =>
      None

  def constructFullName(symbol: Symbol, name: Symbol => String, separator: Symbol => String, skip: Symbol => Boolean): String =
    def constructFullName(symbol: Symbol, suffix: String): String =
      val current = if symbol.isClassDef && symbol.isModuleDef then symbol.companionModule else symbol
      val owner = current.maybeOwner
      val currentName = name(current)

      if owner.exists && suffix.nonEmpty && skip(current) then
        constructFullName(owner, suffix)
      else
        val prefix = if !owner.exists || owner == defn.RootClass then currentName else constructFullName(owner, currentName)

        if prefix.isEmpty || (prefix == "_root_" && suffix.nonEmpty) then
          suffix
        else if suffix.isEmpty then
          prefix
        else
          s"$prefix${separator(current)}$suffix"
    end constructFullName

    constructFullName(symbol, "")
  end constructFullName

  def fullName(symbol: Symbol): String =
    constructFullName(symbol,
      name = _.name,
      separator = symbol => if symbol.isType && !symbol.isPackageDef && !symbol.isModuleDef then "#" else ".",
      skip = symbol => symbol.isAnonymousClass || symbol.isAnonymousFunction || symbol.isPackageObject)
end Commons
