package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait PlacedTransformations:
  this: Component & Commons & ErrorReporter =>
  import quotes.reflect.*

  def transformBody(term: Term, owner: Symbol)(transform: (Term, List[Symbol]) => Term): Term =
    def transformBody(term: Term, owners: List[Symbol]): Term = term match
      case block @ Lambda(arg :: _, expr) if arg.symbol.isImplicit =>
        val Block(List(lambda: DefDef), closure) = block: @unchecked
        val rhs = transformBody(expr, lambda.symbol :: owners)
        Block.copy(block)(List(DefDef.copy(lambda)(lambda.name, lambda.paramss, lambda.returnTpt, Some(rhs))), closure)
      case _ =>
        transform(term, owners).changeOwner(owners.head)

    transformBody(term, List(owner))
  end transformBody

  private def processPlacementBody(term: Term, transform: Option[(Symbol, Term, Option[Term]) => (Term, Option[Term])]) =
    def dropLastExpr(block: Block) = block.statements match
      case (term: Term) +: Nil => (term, false)
      case statements :+ (term: Term) => (Block.copy(block)(statements, term), false)
      case statements => (Block.copy(block)(statements, Literal(UnitConstant())), true)

    def appendExpr(original: Option[Block])(term: Term, expr: Term, dropCoercedUnit: Boolean) = term match
      case Lambda(_, _) => original.fold(Block(List(term), expr)) { Block.copy(_)(List(term), expr) }
      case block @ Block(statements, Literal(UnitConstant())) if dropCoercedUnit => Block.copy(block)(statements, expr)
      case block @ Block(statements, _) => Block.copy(block)(statements :+ block.expr, expr)
      case _ => original.fold(Block(List(term), expr)) { Block.copy(_)(List(term), expr) }

    term match
      case Lambda(List(arg), block @ Block(_, erased: TypeApply))
        if arg.symbol.isImplicit &&
           !(arg.symbol.info =:= TypeRepr.of[Nothing]) &&
           arg.symbol.info <:< types.context &&
           erased.tpe.typeSymbol == symbols.`embedding.on` =>
        val Block(List(lambda @ DefDef(name, args, tpt, _)), closure) = term: @unchecked
        val (body, unitCoersionInserted) = dropLastExpr(block)
        transform.fold(body): transform =>
          val (rhs, expr) = transform(lambda.symbol, body, Some(erased))
          Block.copy(term)(List(DefDef.copy(lambda)(name, args, tpt, Some(expr.fold(rhs) { appendExpr(Some(block))(rhs, _, unitCoersionInserted) }))), closure)

      case Lambda(List(arg), body)
        if arg.symbol.isImplicit &&
           !(arg.symbol.info =:= TypeRepr.of[Nothing]) &&
           arg.symbol.info <:< types.multitierContext =>
        val Block(List(lambda @ DefDef(name, args, tpt, _)), closure) = term: @unchecked
        transform.fold(body): transform =>
          val (rhs, expr) = transform(lambda.symbol, body, None)
          Block.copy(term)(List(DefDef.copy(lambda)(name, args, tpt, Some(expr.fold(rhs) { appendExpr(None)(rhs, _, dropCoercedUnit = false) }))), closure)

      case _ =>
        errorAndCancel("Unexpected shape of placed expression.", term.posInUserCode)
        term
  end processPlacementBody

  def transformPlacementBody(term: Term)(transform: (Symbol, Term, Option[Term]) => (Term, Option[Term])): Term =
    processPlacementBody(term, Some(transform))

  def extractPlacementBody(term: Term): Term =
    processPlacementBody(term, None)

  private object contextVariableCleaner extends SafeTreeMap(quotes):
    private def fallbackIfContextType(term: Term) = term.tpe.asType match
      case '[ Nothing ] | '[ Null ] => term
      case '[ embedding.Placement.Context[p] ] => '{ embedding.Placement.Context.fallback[p] }.asTerm
      case '[ embedding.Multitier.Context ] => '{ embedding.Multitier.Context.fallback }.asTerm
      case _ => term
    override def transformTerm(term: Term)(owner: Symbol) = term match
      case Ident(_) =>
        fallbackIfContextType(term)
      case _ =>
        if (symbols.context.methodMember(term.symbol.name) contains term.symbol) ||
           (symbols.multitierContext.methodMember(term.symbol.name) contains term.symbol) then
          fallbackIfContextType(term)
        else
          super.transformTerm(term)(owner)

  def clearContextVariables(expr: Term)(owner: Symbol): Term =
    contextVariableCleaner.transformTerm(expr)(owner)
end PlacedTransformations
