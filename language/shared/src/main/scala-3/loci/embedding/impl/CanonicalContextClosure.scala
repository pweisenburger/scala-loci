package loci
package embedding
package impl

import components.*
import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.quoted.*
import scala.util.control.NonFatal

@experimental
def inferrableCanonicalPlacementTypeContextClosure[R: Type](using Quotes)(v: Expr[Any]*): Expr[R] =
  import quotes.reflect.*
  import info.*

  object info extends Component.withQuotes(quotes), Commons, Placements, ErrorReporter, PlacedTransformations

  object PlacementEvidence:
    def unapply(evidence: ValDef): Boolean =
      (evidence.symbol.flags is Flags.Synthetic) && !(evidence.tpt.tpe =:= TypeRepr.of[Nothing]) && evidence.tpt.tpe <:< types.context

  object PlacementContext:
    def unapply(term: Term): Option[(ValDef, Term)] = term match
      case MaybeInlined(Block(List(evidence @ PlacementEvidence()), MaybeInlined(expr))) => Some(evidence, expr)
      case _ => None

  object PlacementCompoundStatements:
    def unapply(stats: List[Statement]): Boolean =
      inline val Invalid = 0
      inline val Intermediate = 1
      inline val Valid = 2
      Valid == stats.foldLeft(Intermediate):
        case (result @ (Intermediate | Valid), stat @ ValDef(_, _, _)) if stat.symbol.flags is Flags.Synthetic => result
        case (Intermediate | Valid, MaybeInlined(Lambda(List(arg), NestedPlacementExpression(_)))) if arg.symbol.isImplicit => Valid
        case (Intermediate | Valid, PlacementCompound()) => Valid
        case _ => Invalid

  object PlacementCompound:
    def unapply(term: Term): Boolean = term match
      case MaybeInlined(Inlined(Some(call), _, Block(PlacementCompoundStatements(), _))) => call.symbol.hasAncestor(symbols.and.owner)
      case _ => false

  object PlacementCall:
    def unapply(tree: Tree): Boolean =
      tree.symbol.hasAncestor(symbols.on, symbols.on.companionModule.moduleClass, symbols.and)

  object NestedPlacementExpression:
    def unapply(term: Term): Option[Term] = term match
      case MaybeInlined(Block(List(), expr @ Inlined(Some(PlacementCall()), _, _))) => Some(expr)
      case MaybeInlined(expr @ Inlined(Some(PlacementCall()), _, _)) => Some(expr)
      case MaybeInlined(PlacementCompound()) => Some(term)
      case _ => None

  def makeContextFunctionLiftingPlacementEvidence[T: Type, R: Type](owner: Symbol, tpe: TypeRepr, body: Term) =
    val (evidence, expr) = body match
      case PlacementContext(evidence, expr) => (Some(evidence), expr)
      case _ => (None, body)

    val block @ Block(List(lambda: DefDef), closure @ Closure(method, _)) =
      Lambda(owner, contextMethodType[T, R], (symbol, _) => expr.changeOwner(symbol)): @unchecked
    val result = Block.copy(block)(List(lambda), Closure.copy(closure)(method, Some(tpe)))

    evidence.fold(result): evidence =>
      val privateWithin = if evidence.symbol.flags is Flags.Protected then evidence.symbol.protectedWithin else evidence.symbol.privateWithin
      val symbol = newVal(owner, evidence.name, evidence.tpt.tpe, evidence.symbol.flags, privateWithin.fold(Symbol.noSymbol) { _.typeSymbol })
      Inlined(None, List.empty, Block(List(ValDef(symbol, evidence.rhs)), result))
  end makeContextFunctionLiftingPlacementEvidence

  def namedOwner(symbol: Symbol) =
    symbol findAncestor { symbol => !symbol.isAnonymousFunction } getOrElse symbol

  def clean(tpe: TypeRepr, ensureLocalType: Boolean) =
    val placementType = tpe match
      case AppliedType(tycon, List(t, p)) if tycon.typeSymbol == symbols.`embedding.on` => Some(t, p)
      case _ => tpe.asType match
        case '[ t `on` p ] => Some(TypeRepr.of[t], TypeRepr.of[p])
        case _ => None
    placementType.fold(tpe): (t, p) =>
      val local = ensureLocalType || t.typeSymbol == symbols.`language.Local`
      (t.asType, p.asType) match
        case ('[ t ], '[ p ]) =>
          PlacedClean.cleanType[t] match
            case '[ u ] =>
              val u = if local then symbols.`language.Local`.typeRef.appliedTo(TypeRepr.of[u]) else TypeRepr.of[u]
              symbols.`embedding.on`.typeRef.appliedTo(List(u, TypeRepr.of[p]))
            case _ =>
              tpe

  def canonical(tpe: TypeRepr, placedMarkerOnly: Boolean) =
    PlacementInfo(tpe).fold(tpe): placementInfo =>
      val args @ List(value, peer) = placementInfo.canonicalType.typeArgs: @unchecked
      val canonicalValue = if value <:< TypeRepr.of[Nothing] then symbols.`embedding.of`.typeRef.appliedTo(args) else value
      val canonicalPeer = peer match
        case OrType(_, _) => TypeRepr.of[Any]
        case _ => peer
      val symbol = if placedMarkerOnly then symbols.`embedding.placed` else symbols.`embedding.on`
      symbol.typeRef.appliedTo(List(canonicalValue, canonicalPeer))

  val code = SourceCode(Position.ofMacroExpansion.sourceFile)

  val followedByPlacementCompoundConstruct =
    var start = Position.ofMacroExpansion.end
    while
      start = code.forwardSkipToToken(code.forwardSkipToken(start))
      start < code.length && (code(start) == ')' || code(start) == '}' || code(start) == '.')
    do ()
    val token = code.slice(start, code.forwardSkipToken(start)).mkString
    token == "and" || token == "`and`"

  val (result, syntheticWithoutNestedPlacementExpression) = v.toList map { _.asTerm } match
    case List(PlacementContext(evidence, NestedPlacementExpression(expr))) =>
      val term = Inlined(None, List.empty, Block(List(evidence), Inlined(None, List.empty, expr)))
      (clearContextVariables(term)(Symbol.spliceOwner), None)
    case List(PlacementContext(evidence, expr)) =>
      val term = Inlined(None, List.empty, Block(List(evidence), Inlined(None, List.empty, expr)))
      val tpe = canonical(clean(TypeRepr.of[R], ensureLocalType = false), placedMarkerOnly = followedByPlacementCompoundConstruct)
      (Block(List(term), Ref(symbols.erased).appliedToType(tpe)), Option.when(evidence.name == "<synthetic context>") { term })
    case terms =>
      val localClosures = terms map:
        case term @ NestedPlacementExpression(expr) =>
          val tpe =
            if expr.tpe.typeSymbol == symbols.`embedding.on` then Some(expr.tpe)
            else if expr.tpe.typeSymbol == symbols.`embedding.placed` then Some(symbols.`embedding.on`.typeRef.appliedTo(expr.tpe.typeArgs))
            else None
          tpe.fold(false, term): tpe =>
            PlacementInfo(tpe).fold(false, term): placementInfo =>
              val closure = (placementInfo.peerType.asType, expr.tpe.asType) match
                case ('[ p ], '[ r ]) => makeContextFunctionLiftingPlacementEvidence[embedding.Placement.Context[p], r](Symbol.spliceOwner, placementInfo.canonicalType, expr)
              (placementInfo.modality.local, Inlined(None, List.empty, closure))
        case term =>
          (false, term)
      val (locals, closures) = localClosures.unzip
      val ensureLocalType = !(locals contains false)
      val tpe = canonical(clean(TypeRepr.of[R], ensureLocalType), placedMarkerOnly = followedByPlacementCompoundConstruct)
      (Block(closures, Ref(symbols.erased).appliedToType(tpe)), None)

  val r = result.tpe

  // To make the context function type inferrable, we hack the current context and change its mode to `Pattern`
  // as this mode lets the context function type propagate without resolving the context argument:
  // https://github.com/scala/scala3/blob/3.0.0/compiler/src/dotty/tools/dotc/typer/Typer.scala#L3483
  // https://github.com/scala/scala3/blob/3.1.0/compiler/src/dotty/tools/dotc/typer/Typer.scala#L3547
  // https://github.com/scala/scala3/blob/3.2.0/compiler/src/dotty/tools/dotc/typer/Typer.scala#L3687
  // https://github.com/scala/scala3/blob/3.3.0/compiler/src/dotty/tools/dotc/typer/Typer.scala#L3790
  // https://github.com/scala/scala3/blob/3.4.0/compiler/src/dotty/tools/dotc/typer/Typer.scala#L4030
  //
  // This hack is without unwanted side effects since we ensure that the expanding function
  // is the outer-most in the surrounding val or def.
  // Hence, no further type-checking will happen in the current context.
  try
    r match
      case AppliedType(fun, typeArgs @ List(value, peer)) if fun.typeSymbol == symbols.`embedding.on` =>
        val symbol = namedOwner(Symbol.spliceOwner.owner)

        if (symbol.isDefDef || symbol.isValDef) && !symbol.isLocalDummy && symbol.owner.isClassDef && isMultitierModule(symbol.owner) then
          val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
          val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
          val freshContextClass = Class.forName("dotty.tools.dotc.core.Contexts$FreshContext")
          val modeClass = Class.forName("dotty.tools.dotc.core.Mode")
          val symbolClass = Class.forName("dotty.tools.dotc.core.Symbols$Symbol")
          val symDenotationClass = Class.forName("dotty.tools.dotc.core.SymDenotations$SymDenotation")
          val completerClass = Class.forName("dotty.tools.dotc.typer.Namer$Completer")
          val sourcePositionClass = Class.forName("dotty.tools.dotc.util.SourcePosition")
          val positionedClass = Class.forName("dotty.tools.dotc.ast.Positioned")
          val blockClass = Class.forName("dotty.tools.dotc.ast.Trees$Block")
          val valOrDefDefClass = Class.forName("dotty.tools.dotc.ast.Trees$ValOrDefDef")

          val ctx = quotesImplClass.getMethod("ctx")
          val outersIterator = contextClass.getMethod("outersIterator")
          val owner = freshContextClass.getMethod("owner")
          val setMode = freshContextClass.getMethod("setMode", classOf[Int])
          val denot = symbolClass.getMethod("denot", contextClass)
          val rawParamss = symDenotationClass.getMethod("rawParamss")
          val infoOrCompleter = symDenotationClass.getMethod("infoOrCompleter")
          val original = completerClass.getMethod("original")
          val contains = sourcePositionClass.getMethod("contains", sourcePositionClass)
          val sourcePos = positionedClass.getMethod("sourcePos", contextClass)
          val stats = blockClass.getMethod("stats")
          val expr = blockClass.getMethod("expr")
          val unforcedRhs = valOrDefDefClass.getMethod("unforcedRhs")

          val context = ctx.invoke(quotes)
          val pattern = modeClass.getMethod("Pattern").invoke(null)
          val denotation = denot.invoke(symbol, context)
          val paramss = rawParamss.invoke(denotation)
          val completer = infoOrCompleter.invoke(denotation)

          val hasNoParams = paramss match
            case paramss: List[?] => paramss.isEmpty
            case _ => false

          // check whether the type of the surrounding val or def is still to be inferred
          if completerClass.isInstance(completer) then
            val rhs = unforcedRhs.invoke(original.invoke(completer))
            val rhsTerm =
              if blockClass.isInstance(rhs) then
                stats.invoke(rhs) match
                  case stats: List[?] if stats.isEmpty => expr.invoke(rhs)
                  case _ => rhs
              else
                rhs

            // The position for the term of the application of the `and` extension method for compound placements
            // may miss the final closing brace or parenthesis
            val pos = Position(
              Position.ofMacroExpansion.sourceFile,
              Position.ofMacroExpansion.start,
              code.forwardSkipToToken(Position.ofMacroExpansion.end) + 1)

            // check whether the expanding function is the outer-most in the surrounding val or def
            if contains.invoke(pos, sourcePos.invoke(rhsTerm, context)) == true then
              outersIterator.invoke(context) match
                case outers: Iterator[?] =>
                  outers foreach: context =>
                    if freshContextClass.isInstance(context) && (owner.invoke(context) eq symbol) then
                      setMode.invoke(context, pattern)

                  syntheticWithoutNestedPlacementExpression match
                    case Some(expr) if hasNoParams =>
                      val tpe = symbols.nonplacedType.typeRef.appliedTo(List(types.nonplaced, value))
                      value.asType match
                        case '[ v ] => makeContextFunctionLiftingPlacementEvidence[embedding.Multitier.Context, v](symbol, tpe, expr).asExpr match
                          case result: Expr[R] @unchecked => return result

                    case Some(expr) =>
                      v.head match
                        case result: Expr[R] @unchecked => return result

                    case _ =>
                  end match

                  val tpe = symbols.`language.on`.typeRef.appliedTo(typeArgs)
                  (peer.asType, r.asType) match
                    case ('[ p ], '[ r ]) => makeContextFunctionLiftingPlacementEvidence[embedding.Placement.Context[p], r](symbol, tpe, result).asExpr match
                      case result: Expr[R] @unchecked => return result

                case _ =>
            end if
//          else
//            // If the surrounding val or def has an explicit type annotation,
//            // the `MultitierPreprocessor` can inject a `placed` expression
//            // to improve type inference within the body
//            // (in particular discarding non-Unit values, i.e., insertion of Unit values).
//            // If the surrounding val or def is not placed,
//            // it will not have an `on` placement type and the peer type will be inferred as `Any`.
//            // In such case, we just expand to the unprocessed expression passed to the expanding function
//            // without any added context argument.
//            terms match
//              case List(SyntheticContextParameter(evidence, body))
//                if !(evidence.tpt.tpe =:= TypeRepr.of[Nothing]) &&
//                   evidence.tpt.tpe <:< types.context &&
//                   peer.typeSymbol == defn.AnyClass &&
//                   symbol.info.resultType.typeSymbol != symbols.`language.on` &&
//                   symbol.info.resultType.typeSymbol != symbols.`embedding.on` =>
//                body.asExpr match
//                  case result: Expr[R] @unchecked => return result
//              case _ =>
      case _ =>
  catch
    case NonFatal(e) if e.getClass.getCanonicalName != "scala.quoted.runtime.StopMacroExpansion" =>

  result.asExpr match
    case result: Expr[R] @unchecked => result
end inferrableCanonicalPlacementTypeContextClosure
