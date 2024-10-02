package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait PlacedTransformations:
  this: Component & Commons & ErrorReporter & Placements & NonPlacements =>
  import quotes.reflect.*

  def transformBody(term: Term, owner: Symbol)(transform: (Term, List[Symbol]) => Term): Term =
    transformBody(term, term.tpe, owner): (term, _, owners) =>
      transform(term, owners)

  def transformBody(term: Term, tpe: TypeRepr, owner: Symbol)(transform: (Term, TypeRepr, List[Symbol]) => Term): Term =
    def transformBody(term: Term, tpe: TypeRepr, owners: List[Symbol]): Term = term match
      case block @ Lambda(arg :: _, expr) if arg.symbol.isImplicit && tpe.isContextFunctionType && tpe.typeArgs.nonEmpty =>
        val Block(List(lambda: DefDef), closure) = block: @unchecked
        val rhs = transformBody(expr, tpe.dealias.typeArgs.last, lambda.symbol :: owners)
        Block.copy(block)(List(DefDef.copy(lambda)(lambda.name, lambda.paramss, lambda.returnTpt, Some(rhs))), closure)
      case _ =>
        transform(term, tpe, owners).changeOwner(owners.head)

    transformBody(term, tpe, List(owner))
  end transformBody

  private enum Processing[Result]:
    case Transform(transform: (Symbol, Term, Option[Term]) => (Term, Option[Term])) extends Processing[Term]
    case Extract extends Processing[List[(Term, Option[TypeRepr])]]

  private def processPlacementBody[Result](term: Term, processing: Processing[Result]): Result =
    def dropLastExpr(block: Block) = block.statements match
      case (term: Term) +: Nil => (term, false)
      case statements :+ (term: Term) => (Block.copy(block)(statements, term), false)
      case statements => (Block.copy(block)(statements, Literal(UnitConstant())), true)

    def appendExpr(original: Option[Block])(term: Term, expr: Term, dropCoercedUnit: Boolean) = term match
      case Lambda(_, _) => original.fold(Block(List(term), expr)) { Block.copy(_)(List(term), expr) }
      case block @ Block(statements, Literal(UnitConstant())) if dropCoercedUnit => Block.copy(block)(statements, expr)
      case block @ Block(statements, _) => Block.copy(block)(statements :+ block.expr, expr)
      case _ => original.fold(Block(List(term), expr)) { Block.copy(_)(List(term), expr) }

    def placedLambda(stat: Statement) = stat match
      case Lambda(List(arg), Block(_, erased: TypeApply)) =>
        arg.symbol.isImplicit &&
        !(arg.symbol.info =:= TypeRepr.of[Nothing]) &&
        arg.symbol.info <:< types.context &&
        erased.tpe.typeSymbol == symbols.`embedding.on`
      case _ =>
        false

    def `processPlacedLambda/Singleton`(stat: Statement): Result =
      val Block(List(lambda @ DefDef(name, args, tpt, Some(block @ Block(_, erased)))), closure) = stat: @unchecked
      val (body, unitCoercionInserted) = dropLastExpr(block)
      processing match
        case Processing.Extract =>
          List(body -> Some(erased.tpe.widenTermRefByName))
        case Processing.Transform(transform) =>
          val (rhs, expr) = transform(lambda.symbol, body, Some(erased))
          Block.copy(stat)(List(DefDef.copy(lambda)(name, args, tpt, Some(expr.fold(rhs) { appendExpr(Some(block))(rhs, _, unitCoercionInserted) }))), closure)

    def `processPlacedLambda/PotentialList`(stat: Statement): Result =
      val Block(List(lambda @ DefDef(name, args, tpt, Some(block @ Block(stats, erased)))), closure) = stat: @unchecked
      val placedLambdaList = stats map placedLambda
      if placedLambdaList.nonEmpty && !(placedLambdaList contains false) then
        val exprs = stats map `processPlacedLambda/Singleton`
        processing match
          case Processing.Extract =>
            (exprs: List[List[(Term, Option[TypeRepr])]]).flatten
          case Processing.Transform(_) =>
            val body = Block.copy(block)(exprs, erased)
            Block.copy(stat)(List(DefDef.copy(lambda)(name, args, tpt, Some(body))), closure)
      else
        if placedLambdaList contains true then
          errorAndCancel("Unexpected shape of placed expression.", term.posInUserCode)
        `processPlacedLambda/Singleton`(stat)

    term match
      case _ if placedLambda(term) =>
        `processPlacedLambda/PotentialList`(term)

      case Lambda(List(arg), body)
        if arg.symbol.isImplicit &&
           !(arg.symbol.info =:= TypeRepr.of[Nothing]) &&
           arg.symbol.info <:< types.multitierContext =>
        val Block(List(lambda @ DefDef(name, args, tpt, _)), closure) = term: @unchecked
        processing match
          case Processing.Extract =>
            List(body -> None)
          case Processing.Transform(transform) =>
            val (rhs, expr) = transform(lambda.symbol, body, None)
            Block.copy(term)(List(DefDef.copy(lambda)(name, args, tpt, Some(expr.fold(rhs) { appendExpr(None)(rhs, _, dropCoercedUnit = false) }))), closure)

      case _ =>
        errorAndCancel("Unexpected shape of placed expression.", term.posInUserCode)
        processing match
          case Processing.Extract => List(term -> None)
          case Processing.Transform(transform) => term
  end processPlacementBody

  def transformPlacementBodies(term: Term)(transform: (Symbol, Term, Option[Term]) => (Term, Option[Term])): Term =
    processPlacementBody(term, Processing.Transform(transform))

  def extractPlacementBodies(term: Term): List[(Term, Option[TypeRepr])] =
    processPlacementBody(term, Processing.Extract)

  private object contextVariableCleaner extends SafeTreeMap(quotes):
    private def fallbackIfContextType(term: Term) = term.tpe.asType match
      case '[ Nothing ] | '[ Null ] => term
      case '[ embedding.Placement.Context[p] ] => Ref(symbols.placementContextFallback).appliedToType(TypeRepr.of[p])
      case '[ embedding.Multitier.Context ] => Ref(symbols.multitierContextFallback)
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

  def selectionType(tpe: TypeRepr) = tpe match
    case AppliedType(_, _) | Refinement(_, _, _) =>
      !(tpe =:= TypeRepr.of[Nothing]) &&
      !(tpe <:< types.`language.on`) &&
      !(tpe <:< types.`embedding.on`) &&
      (tpe <:< types.from || tpe <:< types.fromSingle || tpe <:< types.fromMultiple)
    case _ =>
      false

  class PlacementFromPlacedValueTypeEraser extends TypeMap(quotes):
    override def transform(tpe: TypeRepr) =
      val corrected = tpe match
        case AndType(AppliedType(tycon, args), right) if tycon.typeSymbol == symbols.placed && args.last =:= right =>
          symbols.`embedding.on`.typeRef.appliedTo(args.reverse)
        case _ =>
          tpe

      if selectionType(corrected) then
        TypeRepr.of[Unit]
      else
        PlacementInfo(corrected) match
          case Some(placementInfo) =>
            if placementInfo.modality.subjective then
              TypeRepr.of[Unit]
            else
              transform(placementInfo.valueType)
          case _ =>
            NonPlacementInfo(corrected) match
              case Some(nonPlacementInfo) =>
                transform(nonPlacementInfo.valueType)
              case _ =>
                super.transform(corrected)
    end transform
  end PlacementFromPlacedValueTypeEraser
end PlacedTransformations
