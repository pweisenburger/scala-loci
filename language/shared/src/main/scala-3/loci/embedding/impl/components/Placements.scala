package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait Placements:
  this: Component & Commons =>
  import quotes.reflect.*

  enum Modality(val local: Boolean, val subjective: Boolean, val subjectivePeerType: Option[TypeRepr]):
    case None extends Modality(false, false, scala.None)
    case Local extends Modality(true, false, scala.None)
    case Subjective(peerType: TypeRepr) extends Modality(false, true, scala.Some(peerType))

  case class PlacementInfo(tpe: TypeRepr, canonical: Boolean, canonicalType: TypeRepr, valueType: TypeRepr, peerType: TypeRepr, modality: Modality):
    def showCanonical =
      val `subjective.safeShow` = modality.subjectivePeerType.fold(""): peerType =>
        s" ${symbols.`language.per`.name} ${peerType.safeShow(Printer.SafeTypeReprShortCode)}"
      s"${valueType.safeShow(Printer.SafeTypeReprShortCode)}${`subjective.safeShow`} ${symbols.`language.on`.name} ${peerType.safeShow(Printer.SafeTypeReprShortCode)}"

  object PlacementInfo:
    def apply(tpe: TypeRepr): Option[PlacementInfo] =
      def modality(tpe: TypeRepr, peer: TypeRepr, of: Boolean): PlacementInfo = tpe match
        case AppliedType(tycon, args) if tycon.typeSymbol == symbols.`embedding.of` && args.last =:= peer =>
          val info = modality(args.head, peer, of = true)
          if !of || !info.canonical then info else info.copy(canonical = false)
        case Refinement(parent, "on", TypeBounds(lo, hi)) if lo =:= peer && hi =:= peer =>
          val info = modality(parent, peer, of = true)
          if !info.canonical then info else info.copy(canonical = false)
        case AppliedType(tycon, args) if tycon.typeSymbol == symbols.`language.Local` =>
          PlacementInfo(tpe, canonical = true, tpe, args.head, defn.NothingClass.typeRef, Modality.Local)
        case AppliedType(tycon, args) if tycon.typeSymbol == symbols.`language.per` =>
          PlacementInfo(tpe, canonical = true, tpe, args.head, defn.NothingClass.typeRef, Modality.Subjective(args.last))
        case AppliedType(tycon, args) if tycon.typeSymbol == symbols.subjective =>
          PlacementInfo(tpe, canonical = false, symbols.`language.per`.typeRef.appliedTo(args.reverse), args.last, defn.NothingClass.typeRef, Modality.Subjective(args.head))
        case _ =>
          PlacementInfo(tpe, canonical = true, tpe, tpe, defn.NothingClass.typeRef, Modality.None)

      def placementInfo(tpe: TypeRepr): Option[PlacementInfo] = tpe match
        case AppliedType(tycon, List(value, peer)) if tycon.typeSymbol == symbols.`language.on` =>
          Some:
            val info = modality(value, peer, of = false)
            val canonicalType = symbols.`language.on`.typeRef.appliedTo(List(info.canonicalType, peer))
            info.copy(tpe = tpe, canonicalType = canonicalType, peerType = peer)
        case AppliedType(tycon, args @ List(value, peer)) if tycon.typeSymbol == symbols.`embedding.on` =>
          Some:
            val info = modality(value, peer, of = false)
            val canonicalType = symbols.`language.on`.typeRef.appliedTo(List(info.canonicalType, peer))
            info.copy(tpe = tpe, canonical = false, canonicalType = canonicalType, peerType = peer)
        case AndType(AppliedType(tycon, args), right) if tycon.typeSymbol == symbols.placed && args.last =:= right =>
          PlacementInfo(symbols.`embedding.on`.typeRef.appliedTo(args.reverse))
        case _ =>
          None

      tpe match
        case AppliedType(tycon, args @ List(AppliedType(_, List(peerType)), _)) if tycon.typeSymbol == symbols.contextFunction1 && args.head <:< types.context =>
          placementInfo(args.last) collect:
            case placementInfo if placementInfo.peerType =:= peerType && !placementInfo.canonical => placementInfo
        case _ =>
          placementInfo(tpe)
    end apply
  end PlacementInfo

  object PlacedValueReference:
    def unapply(tree: Term): Option[(Term, PlacementInfo)] = tree match
      case Apply(Select(qualifier, names.apply), List(_)) if qualifier.symbol.exists && isMultitierModule(qualifier.symbol.owner) =>
        PlacementInfo(qualifier.tpe.widenTermRefByName.resultType) map { qualifier -> _ }
      case _ =>
        None
  end PlacedValueReference

  object PlacedStatement:
    def unapply(tree: Statement): Option[Statement] = tree match
      case tree: Term =>
        val tpe = tree.tpe
        Option.when(tpe.isContextFunctionType && tpe.contextFunctionResultType.typeSymbol == symbols.`embedding.on`)(tree)
      case tree: Definition =>
        val tpe = tree.symbol.info.resultType
        Option.when(tpe.isContextFunctionType && tpe.typeSymbol == symbols.`language.on`)(tree)
      case _ =>
        None
  end PlacedStatement

  object PlacedAccess:
    object Transmission:
      def unapply(symbol: Symbol) =
        if symbol.isImplicit || symbol.isExtensionMethod then
          symbol.info match
            case PolyTypes(MethodType(_, List(paramType), PolyTypes(MethodType(_, paramTypes, _))))
              if !(paramType =:= TypeRepr.of[Nothing]) &&
                 !(paramType <:< types.`language.on`) &&
                 !(paramType <:< types.`embedding.on`) &&
                 (paramType <:< types.from || paramType <:< types.fromSingle || paramType <:< types.fromMultiple) =>
              val indices = paramTypes.zipWithIndex collect:
                case (tpe, index) if !(tpe =:= TypeRepr.of[Nothing]) && tpe <:< types.transmission => index
              indices match
                case List(index) => Some(index)
                case _ => None
            case _ =>
              None
        else
          None

      private object PolyTypes:
        def unapply(tpe: TypeRepr): Some[TypeRepr] = tpe match
          case PolyType(_, _, PolyTypes(tpe)) => Some(tpe)
          case _ => Some(tpe)
    end Transmission

    def apply(term: Apply, apply: Apply, arg: Term, typeApplies: List[TypeApply], prefix: List[Term], transmission: Term, suffix: List[Term]) =
      Apply.copy(term)(TypeApplies(Apply.copy(apply)(apply.fun, List(arg)), typeApplies), prefix ++ (transmission :: suffix))

    def unapply(term: Term) = term match
      case term @ Apply(TypeApplies(apply @ Apply(fun, List(arg)), typeApplies), args) =>
        term.symbol match
          case Transmission(index) =>
            val (prefix, suffix) = args.splitAt(index)
            Some(term, apply, arg, typeApplies, prefix, suffix.head, suffix.tail)
          case _ =>
            None
      case _ =>
        None

    private object TypeApplies:
      def apply(term: Term, typeApplies: List[TypeApply]): Term = typeApplies match
        case typeApply :: typeApplies => TypeApply.copy(typeApply)(TypeApplies(term, typeApplies), typeApply.args)
        case _ => term

      def unapply(term: Term): Some[(Term, List[TypeApply])] = term match
        case typeApply @ TypeApply(TypeApplies(fun, typeApplies), _) =>
          Some(fun, typeApply :: typeApplies)
        case _ =>
          Some(term, List.empty)
    end TypeApplies
  end PlacedAccess
end Placements
