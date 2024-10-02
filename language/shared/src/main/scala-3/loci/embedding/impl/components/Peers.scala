package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.{experimental, targetName}
import scala.collection.mutable

object Peers:
  private val cache = mutable.Map.empty[Any, Any]

@experimental
trait Peers:
  this: Component & Commons =>
  import quotes.reflect.*

  private val cache = Peers.cache match
    case cache: mutable.Map[(TypeRepr, TypeRef), PeerInfo] @unchecked => cache

  enum Multiplicity:
    case Single, Optional, Multiple

  case class PeerInfo(peerType: TypeRef, parents: List[TypeRef], ties: List[(TypeRef, Multiplicity)])

  object PeerInfo:
    def apply(tpe: TypeRepr): Option[PeerInfo] =
      check(tpe, Left(Position.ofMacroExpansion), None, shallow = false).toOption

    def check(tpe: TypeRepr, pos: Position = Position.ofMacroExpansion): Either[(String, quotes.reflect.Position), PeerInfo] =
      check(tpe, Left(pos), None, shallow = false)

    def check(tree: TypeDef): Either[(String, quotes.reflect.Position), PeerInfo] =
      check(ThisType(tree.symbol.owner).select(tree.symbol), Right(tree), None, shallow = false)

    def check(tree: TypeDef, shallow: Boolean): Either[(String, quotes.reflect.Position), PeerInfo] =
      check(ThisType(tree.symbol.owner).select(tree.symbol), Right(tree), None, shallow)

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

    private def check(tpe: TypeRepr, reference: Either[Position, Tree], qualifier: Option[TypeRepr], shallow: Boolean)
    : Either[(String, Position), PeerInfo] = tpe match
      case tpe: TypeRef if tpe.typeSymbol == defn.AnyClass =>
        Right(PeerInfo(tpe, List.empty, List.empty))

      case tpe: TypeRef =>
        cache.get(qualifier getOrElse tpe.qualifier, tpe) map { Right(_) } getOrElse:
          if !shallow then
            cache += (qualifier getOrElse tpe.qualifier, tpe) -> PeerInfo(tpe, List.empty, List.empty)

          val symbol = tpe.typeSymbol
          val module = if reference.isRight then symbol.owner else Symbol.noSymbol

          val result =
            if symbol.hasAnnotation(symbols.peer) then
              tpe.qualifier.memberType(symbol) match
                case TypeBounds(low: TypeRef, hi) if bottomType(low) =>
                  val ref = reference flatMap:
                    case TypeDef(_, TypeBoundsTree(_, hi)) => Right(hi)
                    case tree => Left(tree.posInUserCode)
                  parentsAndTies(hi, ref, qualifier getOrElse tpe.qualifier, module, shallow) flatMap: (parents, ties) =>
                    validateAndResolveTies(tpe, parents, ties, (reference map { _.posInUserCode }).merge, qualifier getOrElse tpe.qualifier, module) map: ties =>
                      PeerInfo(tpe, parents, ties)

                case TypeBounds(low, hi) =>
                  val pos = reference flatMap:
                    case TypeDef(_, TypeBoundsTree(low, _)) => Right(low.posInUserCode)
                    case TypeDef(_, rhs) => Left(rhs.posInUserCode)
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
                    Left(s"Type alias not allowed for peer specification. Use an upper bound: ${prettyType(s"<: $prettyLow")}", pos.merge)
                  else
                    Left(s"Lower type bound not allowed for peer specification: ${prettyType(s">: ${low.prettyShowFrom(module)}")}", pos.merge)

                case tpe =>
                  val pos = reference flatMap:
                    case TypeDef(_, rhs) => Right(rhs.posInUserCode)
                    case tree => Left(tree.posInUserCode)
                  Left(s"Unexpected type in peer specification: ${prettyType(tpe.prettyShowFrom(module))}", pos.merge)
            else
              Left(s"No peer type: ${prettyAnnotation("@peer")} ${prettyKeyword("type")} ${prettyType(symbol.name)}", (reference map { _.posInUserCode }).merge)
          end result

          if !shallow then
            result match
              case Right(result) => cache += (qualifier getOrElse tpe.qualifier, tpe) -> result
              case _ => cache.remove(qualifier getOrElse tpe.qualifier, tpe)

          result

      case _ =>
        Left(s"No peer type: ${prettyAnnotation("@peer")} ${prettyKeyword("type")}", (reference map { _.posInUserCode }).merge)
    end check

    private inline def checkIfNotShallow(tpe: TypeRepr, reference: Either[Position, Tree], qualifier: Option[TypeRepr], shallow: Boolean) =
      if !shallow then check(tpe, reference, qualifier, shallow) map { _ => () } else Right(())

    private def validateAndResolveTies(peerType: TypeRef, parents: List[TypeRef], ties: List[(TypeRef, Multiplicity)], pos: Position, qualifier: TypeRepr, module: Symbol)
    : Either[(String, Position), List[(TypeRef, Multiplicity)]] =
      def peerModuleMessage =
        Option.unless(isMultitierModule(peerType.typeSymbol.owner)):
          (s"Peer ${prettyType(peerType.prettyShowFrom(module))} is not defined in a multitier module.", pos)

      def referencedPeersNestedModuleMessage =
        def thisTypeIfPossible(tpe: TypeRepr) = tpe match
          case tpe: TypeRef if tpe.typeSymbol.isClassDef => ThisType(tpe.typeSymbol)
          case tpe: TermRef if tpe.termSymbol.isModuleDef => ThisType(tpe.typeSymbol)
          case _ => tpe

        val qualifierType = thisTypeIfPossible(peerType.qualifier)
        val qualifierSymbol = qualifierType.typeSymbol

        def checkPeerNesting(inner: Symbol, outer: Symbol): Boolean =
          inner.exists && isMultitierModule(inner) && (inner == outer || checkPeerNesting(inner.maybeOwner, outer))

        def checkPeerPath(path: TypeRepr): Boolean =
          val tpe = thisTypeIfPossible(path)
          path match
            case _
              if tpe =:= qualifierType && isMultitierModule(qualifierSymbol) ||
                 checkPeerNesting(tpe.typeSymbol, qualifierSymbol) ||
                 checkPeerNesting(qualifierSymbol, tpe.typeSymbol) => true
            case AnnotatedType(underlying, _) => checkPeerPath(underlying)
            case Refinement(parent, _, _) => checkPeerPath(parent)
            case TermRef(qualifier, _) if isMultitierModule(tpe.termSymbol) => checkPeerPath(qualifier)
            case _ => false

        parents.iterator ++ (ties.iterator map { (tie, _) => tie }) collectFirst:
          case parent if !checkPeerPath(parent.qualifier) =>
            (s"Peer ${prettyType(peerType.typeSymbol.name)} defined in module ${prettyType(peerType.qualifier.prettyShowFrom(module))} refers to " +
             s"peer ${prettyType(parent.typeSymbol.name)} defined in module ${prettyType(parent.qualifier.prettyShowFrom(module))}, but the modules are not nested multitier modules.",
             pos)
      end referencedPeersNestedModuleMessage

      def widenedBaseModulePeerTieMessage =
        val overridden =
          peerType.typeSymbol.allOverriddenSymbols.toList collect Function.unlift: symbol =>
            peerType.qualifier.select(symbol) match
              case overridden: TypeRef => Some(overridden, Some(symbol.owner.typeRef))
              case _ => None

        ties collectFirst Function.unlift: (tie, multiplicity) =>
          val optionalTie = symbols.optional.typeRef.appliedTo(tie)
          val singleTie = symbols.single.typeRef.appliedTo(tie)
          (parents.iterator map { _ -> None }) ++ overridden.iterator collectFirst Function.unlift: (base, baseModule) =>
            inline def relation = if baseModule.isDefined then "inherited from module" else "defined for parent peer"

            val widenedTie =
              base.qualifier.memberType(base.typeSymbol).resolvedTypeMemberType(names.tie) flatMap: tpe =>
                if multiplicity == Multiplicity.Multiple then
                  if tpe <:< optionalTie then Some("Multiple", "optional", relation, tie, baseModule getOrElse base)
                  else if tpe <:< singleTie then Some("Multiple", "single", relation, tie, baseModule getOrElse base)
                  else None
                else if multiplicity == Multiplicity.Optional then
                  if tpe <:< singleTie then Some("Optional", "single", relation, tie, baseModule getOrElse base)
                  else None
                else
                  None

            widenedTie map: (peerTie, baseTie, relation, tie, base) =>
              (s"$peerTie tie to peer ${prettyType(tie.prettyShowFrom(module))} defined for peer ${prettyType(peerType.prettyShowFrom(module))} " +
               s"does not conform to $baseTie tie $relation ${prettyType(base.prettyShowFrom(module))}.",
               pos)
      end widenedBaseModulePeerTieMessage

      def resolveParentTies(parents: List[TypeRef]): List[(TypeRef, Multiplicity)] =
        parents.foldLeft(List.empty[(TypeRef, Multiplicity)]): (ties, parent) =>
          val tpe = parent.qualifier.memberType(parent.typeSymbol) match
            case TypeBounds(_, hi) => hi
            case tpe => tpe
          parentsAndTies(tpe, Left(pos), qualifier, module, shallow = true).fold(
            _ => ties,
            (parentParents, parentTies) => ties ++ parentTies ++ resolveParentTies(parentParents))

      val resolvedTies = ties ++ resolveParentTies(parents)

      val sortedTies = resolvedTies sortWith:
        case ((peerType0, _), (peerType1, _)) => peerType0 <:< peerType1

      val distinctTies = sortedTies.foldRight(List.empty[(TypeRef, Multiplicity)]):
        case (tie, List()) =>
          List(tie)
        case (tie0 @ (peer0, multiplicity0), ties @ (peer1, multiplicity1) :: _) =>
          if peer0 =:= peer1 then
            if multiplicity0.ordinal < multiplicity1.ordinal then tie0 :: ties.tail else ties
          else
            tie0 :: ties

      def widenedSubPeerTieMessage =
        distinctTies.tails collectFirst Function.unlift: ties =>
          ties.headOption flatMap: (peer0, multiplicity0) =>
            ties.tail collectFirst:
              case (peer1, multiplicity1) if peer0 <:< peer1 && multiplicity0.ordinal > multiplicity1.ordinal =>
                val (superMultiplicity, subMultiplicity) =
                  if multiplicity1 == Multiplicity.Optional then ("optional", "optional or single")
                  else ("single", "single")
                (s"Tie to peer ${prettyType(peer0.prettyShowFrom(module))} needs to be $subMultiplicity " +
                 s"because tie to super peer ${prettyType(peer1.prettyShowFrom(module))} is $superMultiplicity.",
                 pos)

      peerModuleMessage orElse
      referencedPeersNestedModuleMessage orElse
      widenedBaseModulePeerTieMessage orElse
      widenedSubPeerTieMessage toLeft
      distinctTies
    end validateAndResolveTies

    private def parentsAndTies(tpe: TypeRepr, reference: Either[Position, Tree], qualifier: TypeRepr, module: Symbol, shallow: Boolean)
    : Either[(String, Position), (List[TypeRef], List[(TypeRef, Multiplicity)])] = tpe match
      case tpe: TypeRef =>
        checkIfNotShallow(tpe, reference flatMap { tree => Left(tree.posInUserCode) }, Some(qualifier), shallow) map: _ =>
          (if topType(tpe) then List.empty else List(tpe), List.empty)

      case AndType(left, right) =>
        val (leftRef, rightRef) = reference match
          case Right(Applied(andType, List(leftArg, rightArg))) if andType.symbol == symbols.`&` => (Right(leftArg), Right(rightArg))
          case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
          case _ => (reference, reference)
        parentsAndTies(left, leftRef, qualifier, module, shallow) flatMap: (leftParents, leftTies) =>
          parentsAndTies(right, rightRef, qualifier, module, shallow) map: (rightParents, rightTies) =>
            (leftParents ++ rightParents, leftTies ++ rightTies)

      case OrType(_, _) =>
        val pos = reference match
          case Left(pos) => pos
          case Right(Applied(orType, List(_, _))) if orType.symbol == symbols.`|` => orType.posInUserCode
          case Right(tree) => tree.posInUserCode
        Left(s"Union type not allowed in peer specification: ${prettyType(tpe.prettyShowFrom(module))}", pos)

      case Refinement(parent: TypeRef, names.tie, info) => info match
        case TypeBounds(low: TypeRef, hi) if bottomType(low) =>
          val (parentRef, hiRef) = reference match
            case Right(Refined(tpt, List(TypeDef(names.tie, TypeBoundsTree(_, hi))))) => (Right(tpt), Right(hi))
            case Right(Refined(tpt, refinement :: _)) => (Right(tpt), Left(refinement.posInUserCode))
            case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
            case _ => (reference, reference)
          checkIfNotShallow(parent, parentRef flatMap { tree => Left(tree.posInUserCode) }, Some(qualifier), shallow) flatMap: _ =>
            ties(hi, hiRef, qualifier, module, shallow) flatMap: ties =>
              parentsAndTies(parent, parentRef, qualifier, module, shallow) map: (parentParents, parentTies) =>
                (parentParents, parentTies ++ ties)

        case TypeBounds(low, hi) =>
          val pos = reference flatMap:
            case Refined(_, List(TypeDef(names.tie, TypeBoundsTree(low, _)))) => Right(low.posInUserCode)
            case Refined(_, refinement :: _) => Left(refinement.posInUserCode)
            case tree => Left(tree.posInUserCode)
          if pos.isLeft && low =:= hi then
            Left(s"Type alias not allowed for peer tie specification. Use an upper bound: ${prettyType(s"<: ${low.prettyShowFrom(module)}")}", pos.merge)
          else
            Left(s"Lower type bound not allowed for peer tie specification: ${prettyType(s">: ${low.prettyShowFrom(module)}")}", pos.merge)

        case _ =>
          Left(s"Unexpected type in peer tie specification: ${prettyType(info.prettyShowFrom(module))}", (reference map { _.posInUserCode }).merge)

      case Refinement(_, name, _) =>
        Left(s"Unexpected type member in peer specification: ${prettyKeyword("type")} ${prettyType(name)}", (reference map { _.posInUserCode }).merge)

      case _ =>
        Left(s"Unexpected type in peer specification: ${prettyType(tpe.prettyShowFrom(module))}", (reference map { _.posInUserCode }).merge)
    end parentsAndTies

    private def ties(tpe: TypeRepr, reference: Either[Position, Tree], qualifier: TypeRepr, module: Symbol, shallow: Boolean)
    : Either[(String, Position), List[(TypeRef, Multiplicity)]] = tpe match
      case tpe: TypeRef if topType(tpe) =>
        Right(List.empty)

      case AndType(left, right) =>
        val (leftRef, rightRef) = reference match
          case Right(Applied(andType, List(leftArg, rightArg))) if andType.symbol == symbols.`&` => (Right(leftArg), Right(rightArg))
          case Right(tree) => (Left(tree.posInUserCode), Left(tree.posInUserCode))
          case _ => (reference, reference)
        ties(left, leftRef, qualifier, module, shallow) flatMap: left =>
          ties(right, rightRef, qualifier, module, shallow) map:
            left ++ _

      case OrType(_, _) =>
        val pos = reference match
          case Left(pos) => pos
          case Right(Applied(orType, List(_, _))) if orType.symbol == symbols.`|` => orType.posInUserCode
          case Right(tree) => tree.posInUserCode
        Left(s"Union type not allowed in peer tie specification: ${prettyType(tpe.prettyShowFrom(module))}", pos)

      case AppliedType(tycon, List(MaybeLazyRef(arg: TypeRef))) =>
        object MultiplicityName:
          def unapply(name: String) =
            name == symbols.single.name || name == symbols.optional.name || name == symbols.multiple.name
        val (tyconPos, argPos) = reference match
          case Left(pos) => (pos, pos)
          case Right(Applied(tpt @ (TypeIdent(MultiplicityName()) | TypeSelect(_, MultiplicityName())), List(arg))) => (tpt.posInUserCode, arg.posInUserCode)
          case Right(tree) => (tree.posInUserCode, tree.posInUserCode)
        val symbol = tycon.typeSymbol
        val multiplicity =
          if symbol == symbols.single then Right(Multiplicity.Single)
          else if symbol == symbols.optional then Right(Multiplicity.Optional)
          else if symbol == symbols.multiple then Right(Multiplicity.Multiple)
          else Left(
            s"Unexpected multiplicity in peer tie specification: ${prettyType(symbol.name)}\n" +
            s"Expected one of: ${prettyType(symbols.single.name)}, ${prettyType(symbols.optional.name)}, ${prettyType(symbols.multiple.name)}",
            tyconPos)
        multiplicity flatMap: multiplicity =>
          checkIfNotShallow(arg, Left(argPos), Some(qualifier), shallow) map: _ =>
            List(arg -> multiplicity)

      case _ =>
        Left(s"Unexpected type in peer tie specification: ${prettyType(tpe.prettyShowFrom(module))}", (reference map { _.posInUserCode }).merge)
    end ties

    private object MaybeLazyRef:
      def unapply(tpe: TypeRepr) = Some(tpe.stripLazyRef)

    private def topType(tpe: TypeRef) =
      val symbol = tpe.typeSymbol
      symbol == defn.AnyClass || symbol == defn.AnyRefClass || symbol == defn.ObjectClass

    private def bottomType(tpe: TypeRef) =
      tpe.typeSymbol == defn.NothingClass
  end PeerInfo
end Peers
