package loci
package embedding
package impl

import communicator.*
import messaging.*
import runtime.*
import utility.reflectionExtensions.*
import scala.quoted.*

object Connections:
  def connect[P: Type](connector: Expr[Connector[ConnectionsBase.Protocol]])(using Quotes): Expr[Connections] =
    '{ embedding.Connections.connect(${signature[P]}, $connector) }

  def connect[P: Type](
      factory: Expr[ConnectionSetupFactory[ConnectionsBase.Protocol]],
      url: Expr[String],
      props: Expr[ConnectionSetupFactory.Properties])(using Quotes): Expr[Connections] =
    '{ embedding.Connections.connect(${signature[P]}, $factory, $url, $props) }

  def listen[P: Type](listener: Expr[Listener[ConnectionsBase.Protocol]])(using Quotes): Expr[Connections] =
    '{ embedding.Connections.listen(${signature[P]}, $listener) }

  def listen[P: Type](
      factory: Expr[ConnectionSetupFactory[ConnectionsBase.Protocol]],
      url: Expr[String],
      props: Expr[ConnectionSetupFactory.Properties])(using Quotes): Expr[Connections] =
    '{ embedding.Connections.listen(${signature[P]}, $factory, $url, $props) }

  private def signature[P: Type](using Quotes) =
    val engine = ResolverEngine(quotes)

    import quotes.reflect.*
    import engine.*

    val tpe = TypeRepr.of[P]

    tpe.maybePathTerm.fold(report.errorAndAbort(s"No path to multitier module for peer type: ${prettyShowType(tpe)}")): path =>
      if !isMultitierModule(path.symbol) then
        report.errorAndAbort(s"Not a @multitier module: ${prettyShowTerm(path)}")

      PeerInfo.check(tpe).left foreach:
        report.errorAndAbort(_, _)

      path.select(peerSignature(path.symbol, tpe.typeSymbol)).asExprOf[Peer.Signature]
  end signature
end Connections
