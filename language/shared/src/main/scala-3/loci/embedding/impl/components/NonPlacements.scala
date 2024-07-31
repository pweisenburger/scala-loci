package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait NonPlacements:
  this: Component & Commons =>
  import quotes.reflect.*

  case class NonPlacementInfo(tpe: TypeRepr, valueType: TypeRepr)

  object NonPlacementInfo:
    def apply(tpe: TypeRepr): Option[NonPlacementInfo] =
      Option.when(!(tpe =:= TypeRepr.of[Nothing]) && tpe <:< types.nonplacedType):
        NonPlacementInfo(tpe, tpe.widenDealias.typeArgs.last)

  object NonPlacedValueReference:
    def unapply(tree: Term): Option[(Term, NonPlacementInfo)] = tree match
      case Apply(Select(qualifier, names.apply), List(_)) if qualifier.symbol.exists && isMultitierModule(qualifier.symbol.owner) =>
        NonPlacementInfo(qualifier.tpe.widenTermRefByName.resultType) map { qualifier -> _ }
      case _ =>
        None

  object NonPlacedStatement:
    def unapply(tree: Statement): Option[Statement] =
      val tpe = tree match
        case tree: Term => Some(tree.tpe)
        case tree: Definition => Some(tree.symbol.info.resultType)
        case _ => None
      Option.when(tpe exists { tpe => !(tpe =:= TypeRepr.of[Nothing]) && tpe <:< types.nonplacedType })(tree)

  object NonPlacedArgumentApplication:
    def unapply(term: Term): Option[Term] = term match
      case Apply(fun, List(_)) if hasSyntheticMultitierContextArgument(fun.symbol) =>
        fun.tpe match
          case MethodType(_, _, _: MethodOrPoly) => None
          case MethodType(_, List(_), _) => Some(fun)
          case _ => None
      case _ =>
        None
end NonPlacements
