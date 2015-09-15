package retier
package impl
package engine.generators

import engine._
import scala.reflect.macros.blackbox.Context

trait PeerImplementationGenerator { this: Generation =>
  val c: Context
  import c.universe._

  val generatePeerImplementations = UniformAggregation[
    EnclosingContext with PeerDefinition with
    PlacedStatement with PlacedAbstraction with
    PeerConnectionMultiplicity] {
      aggregator =>

    echo(verbose = true, " Generating peer implementations")

    val synthetic = Flag.SYNTHETIC
    val peerTypes = aggregator.all[PeerDefinition] map { _.peerType }
    val enclosingName = aggregator.all[EnclosingContext].head.name

    class SelfReferenceChanger(originalName: Name, name: TypeName)
        extends Transformer {
      val originalTypeName = originalName.toTypeName
      val originalTermName = originalName.toTermName

      def isPlaced(tpe: Type): Boolean = tpe <:< types.localOn

      def isPlaced(tree: Tree): Boolean =
        isPlaced(tree.tpe) ||
        (tree.symbol.isMethod &&
         isPlaced(tree.symbol.asMethod.accessed.typeSignature.finalResultType))

      override def transform(tree: Tree) = tree match {
        case ClassDef(_, `originalTypeName`, _, _) => tree
        case ModuleDef(_, `originalTermName`, _) => tree
        case Select(This(`originalTypeName`), _)
          if !tree.isRetierSynthetic && !isPlaced(tree) => tree
        case This(`originalTypeName`)
          if !tree.isRetierSynthetic => This(name)
        case _ => super.transform(tree)
      }
    }

    object SelfReferenceChanger {
      def apply(originalName: Name, name: Name) =
        new SelfReferenceChanger(originalName, name.toTypeName)
    }

    def peerPlacedAbstractions(peerType: Type) =
      aggregator.all[PlacedAbstraction] filter {
        _.peerType =:= peerType
      }

    def peerConnectionMultiplicities(peerType: Type) =
      aggregator.all[PeerConnectionMultiplicity] filter {
        _.peerType =:= peerType
      }

    def peerPlacedStatements(peerType: Type) =
      aggregator.all[PlacedStatement] collect {
        case PlacedStatement(
            definition @ ValDef(mods, name, _, _),
            `peerType`, _, Some(declTypeTree), _, expr) =>
          internal setPos (
            SelfReferenceChanger(enclosingName, names.peer) transform
              ValDef(mods, name, declTypeTree, expr),
            definition.pos)

        case PlacedStatement(
            definition @ DefDef(mods, name, tparams, vparamss, _, _),
            `peerType`, _, Some(declTypeTree), _, expr) =>
          internal setPos (
            SelfReferenceChanger(enclosingName, names.peer) transform
              DefDef(mods, name, tparams, vparamss, declTypeTree, expr),
            definition.pos)

        case PlacedStatement(tree, `peerType`, _, None, _, expr) =>
          SelfReferenceChanger(enclosingName, names.peer) transform expr
      }

    def peerImplementationParents(parents: List[Tree]) = parents map {
      case parent if parent.tpe =:= types.peer =>
        trees.PeerImpl

      case parent @ tq"$expr.$tpnamePeer[..$tpts]"
          if parent.tpe <:< types.peer =>
        if (!(peerTypes exists { parent.tpe <:< _ })) {
          if ((parent.tpe.dealias.companion member names.peer) == NoSymbol)
            c.abort(parent.pos,
              "cannot access peer type implementation " +
              "(maybe peer definition was not placed " +
              "inside `multitier` environment)")
        }

        val name = tpnamePeer.toTermName
        tq"$expr.$name.${names.peer}[..$tpts]"

      case parent =>
        parent
    }

    def processPeerCompanion(peerDefinition: PeerDefinition) = {
      val PeerDefinition(_, peerName, peerType, typeArgs, args, parents, mods,
        _, isClass, companion) = peerDefinition

      val abstractions = peerPlacedAbstractions(peerType)
      val statements = peerPlacedStatements(peerType)
      val implParents = peerImplementationParents(parents)

      import trees._
      import names._

      val syntheticMods = Modifiers(
        mods.flags | Flag.SYNTHETIC, mods.privateWithin, mods.annotations)

      val dispatchImpl =
        q"""$synthetic override def $dispatch(
                request: $String,
                id: $AbstractionId,
                ref: $AbstractionRef): $Try[$String] =
              id match {
                case ..${abstractions map { _.dispatchClause } }
                case _ => super.$dispatch(request, id, ref)
              }
         """

      val systemImpl = q"$synthetic override lazy val $system = new $System"

      val peerImpl =
        if (isClass)
          q"""$syntheticMods class $peer[..$typeArgs](...$args)
                  extends ..$implParents {
                $systemImpl
                $dispatchImpl
                ..$statements
          }"""
        else
          q"""$syntheticMods trait $peer[..$typeArgs]
                  extends ..$implParents {
                $systemImpl
                $dispatchImpl
                ..$statements
          }"""

      val peerInterface =
        q"""$synthetic object $interface {
              ..${abstractions flatMap { _.interfaceDefinitions } }
        }"""

      val generatedCompanion = companion match {
        case Some(q"""$mods object $tname
                    extends { ..$earlydefns } with ..$parents { $self =>
                    ..$stats
                  }""") =>
          q"""$mods object $tname
                  extends { ..$earlydefns } with ..$parents { $self =>
                $peerInterface
                $peerImpl
                ..$stats
          }"""

        case _ =>
          q"""$synthetic object ${peerName.toTermName} {
                $peerInterface
                $peerImpl
          }"""
      }

      peerDefinition.copy(companion = Some(generatedCompanion))
    }

    def processPeerDefinition(peerDefinition: PeerDefinition) = {
      val PeerDefinition(_, peerName, peerType, typeArgs, args, parents, mods,
        stats, isClass, _) = peerDefinition

      val multiplicities = peerConnectionMultiplicities(peerType)

      import trees._
      import names._

      stats foreach {
        case stat: ValOrDefDef if stat.name == connection =>
          c.abort(stat.pos,
            s"member of name `$connection` not allowed in peer definitions")
        case _ =>
      }

      val hasPeerParents = parents exists { parent =>
        parent.tpe <:< types.peer && parent.tpe =:!= types.peer
      }

      val peerMultiplicities = multiplicities map {
        case PeerConnectionMultiplicity( _, connectedPeer,
            connectionMultiplicity) =>
          q"($peerTypeOf[$connectedPeer], $connectionMultiplicity)"
      }

      val peerConnections =
        if (peerMultiplicities.nonEmpty || !hasPeerParents)
          q"$Map[$PeerType, $ConnectionMultiplicity](..$peerMultiplicities)"
        else
          q"super.$connection"

      val connectionImpl = q"$synthetic def $connection = $peerConnections"

      val generatedStats = connectionImpl :: stats
      val generatedTree =
        if (isClass)
          q"""$mods class $peerName[..$typeArgs](...$args)
                  extends ..$parents {
                ..$generatedStats
          }"""
        else
          q"""$mods trait $peerName[..$typeArgs]
                  extends ..$parents {
                ..$generatedStats
          }"""

      peerDefinition.copy(tree = generatedTree, stats = generatedStats)
    }

    val definitions = aggregator.all[PeerDefinition] map
      (processPeerCompanion _ compose processPeerDefinition _)

    echo(verbose = true,
      s"  [${definitions.size} peer definitions generated, existing replaced]")

    aggregator replace definitions
  }
}
