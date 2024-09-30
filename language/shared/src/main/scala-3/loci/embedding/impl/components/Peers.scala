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
    case Single, Optional, Multiple

  case class PeerInfo(peerType: TypeRepr, parents: List[TypeRepr], ties: List[(TypeRepr, Multiplicity)])

  object PeerInfo:
    def apply(tpe: TypeRepr): Option[PeerInfo] =
      check(tpe, Left(Position.ofMacroExpansion)).toOption

    def check(tpe: TypeRepr, pos: Position = Position.ofMacroExpansion): Either[(String, quotes.reflect.Position), PeerInfo] =
      check(tpe, Left(pos))

    def check(tree: TypeDef): Either[(String, quotes.reflect.Position), PeerInfo] =
      check(ThisType(tree.symbol.owner).select(tree.symbol), Right(tree.rhs))

    private def check(tpe: TypeRepr, reference: Either[Position, Tree]): Either[(String, Position), PeerInfo] = tpe match
      case tpe: TypeRef if tpe.typeSymbol == defn.AnyClass =>
        Right(PeerInfo(tpe, List.empty, List.empty))
      case tpe: TypeRef =>
        val symbol = tpe.typeSymbol
        val module = if reference.isRight then symbol.owner else Symbol.noSymbol
        if tpe.typeSymbol.hasAnnotation(symbols.peer) then
          tpe.qualifier.memberType(symbol) match
            case TypeBounds(low: TypeRef, hi) if bottomType(low) =>
              val ref = reference flatMap:
                case TypeBoundsTree(_, hi) => Right(hi)
                case tree => Left(tree.posInUserCode)
              parentsAndTies(hi, ref, module) map { PeerInfo(tpe, _, _) }
            case TypeBounds(low, hi) =>
              val pos = reference flatMap:
                case TypeBoundsTree(low, _) => Right(low.posInUserCode)
                case tree => Left(tree.posInUserCode)
              if pos.isLeft && low =:= hi then
                val prettyLow = low match
                  case Refinement(parent: TypeRef, name, info) if topType(parent) =>
                    val prettyLow = Refinement(defn.AnyClass.typeRef, name, info).prettyShowFrom(module)
                    if prettyLow startsWith "Any{" then prettyLow.drop(3)
                    else if prettyLow startsWith "Any {" then prettyLow.drop(4)
                    else prettyLow
                  case _ =>
                    low.prettyShowFrom(module)
                Left(s"Type alias not allowed for peer specification.\nUse an upper bound: <: $prettyLow", pos.merge)
              else
                Left(s"Lower type bound not allowed for peer specification: >: ${low.prettyShowFrom(module)}", pos.merge)
            case tpe =>
              Left(s"Unexpected type in peer specification: ${tpe.prettyShowFrom(module)}", (reference map { _.posInUserCode }).merge)
        else
          Left(s"No peer type: @peer type ${symbol.name}", (reference map { _.posInUserCode }).merge)
      case _ =>
        Left("No peer type: @peer type", (reference map { _.posInUserCode }).merge)

    @targetName("ofModuleSymbol")
    def ofModule(symbol: Symbol): List[PeerInfo] =
      ofModule(ThisType(symbol))

    @targetName("ofModuleType")
    def ofModule(tpe: TypeRepr): List[PeerInfo] =
      val (peers, _) =
        tpe.baseClasses.foldLeft(List.empty[PeerInfo], Set.empty[Symbol]):
          case ((peers, overridden), symbol) =>
            val declaredPeers = symbol.declarations flatMap: symbol =>
              if symbol.isType && !(symbol.flags is Flags.Synthetic) && !(symbol.flags is Flags.Artifact) && !(overridden contains symbol) then
                PeerInfo(tpe.select(symbol))
              else
                None
            val overriddenPeers = declaredPeers.iterator flatMap: peerInfo =>
              val symbol = peerInfo.peerType.typeSymbol
              Iterator(symbol) ++ symbol.allOverriddenSymbols
            (peers ++ declaredPeers, overridden ++ overriddenPeers)
      PeerInfo(defn.AnyClass.typeRef, List.empty, List.empty) :: peers

    private def parentsAndTies(tpe: TypeRepr, reference: Either[Position, Tree], module: Symbol): Either[(String, Position), (List[TypeRepr], List[(TypeRepr, Multiplicity)])] = tpe match
      case tpe: TypeRef =>
        Right(if topType(tpe) then List.empty else List(tpe), List.empty)
      case AndType(left, right) =>
        val (leftRef, rightRef) = reference match
          case Right(Applied(TypeIdent("&") | TypeSelect(_, "&"), List(leftArg, rightArg))) => (Right(leftArg), Right(rightArg))
          case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
          case _ => (reference, reference)
        parentsAndTies(left, leftRef, module) flatMap: (leftParents, leftTies) =>
          parentsAndTies(right, rightRef, module) map: (rightParents, rightTies) =>
            (leftParents ++ rightParents, leftTies ++ rightTies)
      case OrType(_, _) =>
        val pos = reference match
          case Left(pos) => pos
          case Right(Applied(tpt @ (TypeIdent("|") | TypeSelect(_, "|")), List(_, _))) => tpt.posInUserCode
          case Right(tree) => tree.posInUserCode
        Left(s"Union type not allowed in peer specification: ${tpe.prettyShowFrom(module)}", pos)
      case Refinement(parent: TypeRef, names.tie, info) => info match
        case TypeBounds(low: TypeRef, hi) if bottomType(low) =>
          val (parentRef, hiRef) = reference match
            case Right(Refined(tpt, List(TypeDef(names.tie, TypeBoundsTree(_, hi))))) => (Right(tpt), Right(hi))
            case Right(Refined(tpt, refinement :: _)) => (Right(tpt), Left(refinement.posInUserCode))
            case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
            case _ => (reference, reference)
          ties(hi, hiRef, module) flatMap: ties =>
            parentsAndTies(parent, parentRef, module) map: (parentParents, parentTies) =>
              (parentParents, parentTies ++ ties)
        case TypeBounds(low, hi) =>
          val pos = reference flatMap:
            case Refined(_, List(TypeDef(names.tie, TypeBoundsTree(low, _)))) => Right(low.posInUserCode)
            case Refined(_, refinement :: _) => Left(refinement.posInUserCode)
            case tree => Left(tree.posInUserCode)
          if pos.isLeft && low =:= hi then
            Left(s"Type alias not allowed for peer tie specification.\nUse an upper bound: <: ${low.prettyShowFrom(module)}", pos.merge)
          else
            Left(s"Lower type bound not allowed for peer tie specification: >: ${low.prettyShowFrom(module)}", pos.merge)
        case _ =>
          Left(s"Unexpected type in peer tie specification: ${info.prettyShowFrom(module)}", (reference map { _.posInUserCode }).merge)
      case Refinement(_, name, _) =>
        Left(s"Unexpected type member in peer specification: type $name", (reference map { _.posInUserCode }).merge)
      case _ =>
        Left(s"Unexpected type in peer specification: ${tpe.prettyShowFrom(module)}", (reference map { _.posInUserCode }).merge)

    private def ties(tpe: TypeRepr, reference: Either[Position, Tree], module: Symbol): Either[(String, Position), List[(TypeRepr, Multiplicity)]] = tpe match
      case tpe: TypeRef if topType(tpe) =>
        Right(List.empty)
      case AndType(left, right) =>
        val (leftRef, rightRef) = reference match
          case Right(Applied(TypeIdent("&") | TypeSelect(_, "&"), List(leftArg, rightArg))) => (Right(leftArg), Right(rightArg))
          case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
          case _ => (reference, reference)
        ties(left, leftRef, module) flatMap { left => ties(right, rightRef, module) map { left ++ _ } }
      case OrType(_, _) =>
        val pos = reference match
          case Left(pos) => pos
          case Right(Applied(tpt @ (TypeIdent("|") | TypeSelect(_, "|")), List(_, _))) => tpt.posInUserCode
          case Right(tree) => tree.posInUserCode
        Left(s"Union type not allowed in peer tie specification: ${tpe.prettyShowFrom(module)}", pos)
      case AppliedType(tycon, List(arg)) =>
        object MultiplicityName:
          def unapply(name: String) =
            name == symbols.single.name || name == symbols.optional.name || name == symbols.multiple.name
        val pos = reference match
          case Left(pos) => pos
          case Right(Applied(tpt @ (TypeIdent(MultiplicityName()) | TypeSelect(_, MultiplicityName())), List(_))) => tpt.posInUserCode
          case Right(tree) => tree.posInUserCode
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
        Left(s"Unexpected type in peer tie specification: ${tpe.prettyShowFrom(module)}", (reference map { _.posInUserCode }).merge)

    private def topType(tpe: TypeRef) =
      val symbol = tpe.typeSymbol
      symbol == defn.AnyClass || symbol == defn.AnyRefClass || symbol == defn.ObjectClass

    private def bottomType(tpe: TypeRef) =
      tpe.typeSymbol == defn.NothingClass
  end PeerInfo
end Peers
