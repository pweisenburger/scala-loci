package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.{experimental, targetName}

@experimental
trait Peers:
  this: Component & Commons =>
  import quotes.reflect.*

  enum Multiplicity:
    case Single
    case Optional
    case Multiple

  case class PeerInfo(peerType: TypeRepr, parents: List[TypeRepr], ties: List[(TypeRepr, Multiplicity)], pos: Position)

  object PeerInfo:
    def apply(tpe: TypeRepr): Option[PeerInfo] =
      check(tpe, Position.ofMacroExpansion).toOption

    def apply(tpe: TypeRepr, pos: Position): Option[PeerInfo] =
      check(tpe, pos).toOption

    def check(tpe: TypeRepr): Either[(String, Position), PeerInfo] =
      check(tpe, Position.ofMacroExpansion)

    def check(tpe: TypeRepr, pos: Position): Either[(String, Position), PeerInfo] = tpe match
      case tpe: TypeRef if tpe.typeSymbol == defn.AnyClass =>
        Right(PeerInfo(tpe, List.empty, List.empty, pos))
      case tpe: TypeRef =>
        val symbol = tpe.typeSymbol
        val position = if symbol.flags is Flags.Synthetic then pos else symbol.pos getOrElse pos
        if tpe.typeSymbol.hasAnnotation(symbols.peer) then
          tpe.qualifier.memberType(symbol) match
            case TypeBounds(low: TypeRef, hi) =>
              if bottomType(low) then
                parentsAndTies(hi, pos) map { (parents, ties) => PeerInfo(tpe, parents, ties, pos) }
              else
                Left(s"Lower type bound not allowed in peer specification: >: ${low.safeShow(Printer.SafeTypeReprShortCode)}", position)
            case tpe =>
              Left(s"Unexpected type in peer specification: ${tpe.safeShow(Printer.SafeTypeReprShortCode)}", position)
        else
          Left(s"No peer type: @peer type ${symbol.name}", position)
      case _ =>
        Left("No peer type: @peer type", pos)

    @targetName("ofModuleSymbol")
    def ofModule(symbol: Symbol): List[PeerInfo] =
      ofModule(ThisType(symbol))

    @targetName("ofModuleType")
    def ofModule(tpe: TypeRepr): List[PeerInfo] =
      val (peers, _) =
        tpe.baseClasses.foldLeft(List.empty[PeerInfo], Set.empty[Symbol]):
          case ((peers, overridden), symbol) =>
            val declaredPeers = symbol.declarations flatMap: symbol =>
              if symbol.isType && !(symbol.flags is Flags.Synthetic) && !(overridden contains symbol) then
                PeerInfo(tpe.select(symbol), symbol.pos getOrElse Position.ofMacroExpansion)
              else
                None
            val overriddenPeers = declaredPeers.iterator flatMap: peerInfo =>
              val symbol = peerInfo.peerType.typeSymbol
              Iterator(symbol) ++ symbol.allOverriddenSymbols
            (peers ++ declaredPeers, overridden ++ overriddenPeers)
      PeerInfo(defn.AnyClass.typeRef, List.empty, List.empty, Position.ofMacroExpansion) :: peers

    private def parentsAndTies(tpe: TypeRepr, pos: Position): Either[(String, Position), (List[TypeRepr], List[(TypeRepr, Multiplicity)])] = tpe match
      case tpe: TypeRef =>
        Right((if topType(tpe) then List.empty else List(tpe), List.empty))
      case AndType(left, right) =>
        parentsAndTies(left, pos) flatMap: (leftParents, leftTies) =>
          parentsAndTies(right, pos) map: (rightParents, rightTies) =>
            (leftParents ++ rightParents, leftTies ++ rightTies)
      case OrType(_, _) =>
        Left(s"Union type not allowed in peer specification: ${tpe.safeShow(Printer.SafeTypeReprShortCode)}", pos)
      case Refinement(parent: TypeRef, names.tie, info) => info match
        case TypeBounds(low: TypeRef, hi) =>
          if bottomType(low) then
            ties(hi, pos) flatMap: ties =>
              parentsAndTies(parent, pos) map: (parentParents, parentTies) =>
                (parentParents, parentTies ++ ties)
          else
            Left(s"Lower type bound not allowed for peer tie specification: >: ${low.safeShow(Printer.SafeTypeReprShortCode)}", pos)
        case _ =>
          Left(s"Unexpected type in peer tie specification: ${info.safeShow(Printer.SafeTypeReprShortCode)}", pos)
      case _ =>
        Left(s"Unexpected type in peer specification: ${tpe.safeShow(Printer.SafeTypeReprShortCode)}", pos)

    private def ties(tpe: TypeRepr, pos: Position): Either[(String, Position), List[(TypeRepr, Multiplicity)]] = tpe match
      case tpe: TypeRef if topType(tpe) =>
        Right(List.empty)
      case AndType(left, right) =>
        ties(left, pos) flatMap { left => ties(right, pos) map { left ++ _ } }
      case OrType(_, _) =>
        Left(s"Union type not allowed in peer tie specification: ${tpe.safeShow(Printer.SafeTypeReprShortCode)}", pos)
      case AppliedType(tycon, List(arg)) =>
        val symbol = tycon.typeSymbol
        val multiplicity =
          if symbol == symbols.single then Right(Multiplicity.Single)
          else if symbol == symbols.optional then Right(Multiplicity.Optional)
          else if symbol == symbols.multiple then Right(Multiplicity.Multiple)
          else Left(
            s"Unexpected multiplicity in peer tie specification: ${symbol.name} " +
            s"(expected one of: ${symbols.single.name}, ${symbols.optional.name}, ${symbols.multiple.name})",
            pos)
        multiplicity map { multiplicity => List(arg.stripLazyRef -> multiplicity) }
      case _ =>
        Left(s"Unexpected type in peer tie specification: ${tpe.safeShow(Printer.SafeTypeReprShortCode)}", pos)

    private def topType(tpe: TypeRef) =
      val symbol = tpe.typeSymbol
      symbol == defn.AnyClass || symbol == defn.AnyRefClass || symbol == defn.ObjectClass

    private def bottomType(tpe: TypeRef) =
      tpe.typeSymbol == defn.NothingClass
  end PeerInfo
end Peers
