package loci

import embedding.*
import scala.annotation.{compileTimeOnly, experimental}

package object language {
//  def connect[P](setup: Connector[ConnectionsBase.Protocol]): Connections =
//    macro impl.Connections.setup
//  def connect[P](factory: ConnectionSetupFactory[ConnectionsBase.Protocol])(
//      /* url: String, props: ConnectionSetupFactory.Properties */ args: Any*): Connections =
//    macro impl.Connections.factory
//
//  def listen[P](setup: Listener[ConnectionsBase.Protocol]): Connections =
//    macro impl.Connections.setup
//  def listen[P](factory: ConnectionSetupFactory[ConnectionsBase.Protocol])(
//      /* url: String, props: ConnectionSetupFactory.Properties */ args: Any*): Connections =
//    macro impl.Connections.factory

//  object placed extends On.Placed
//
//  object on extends Select[Run]:
//    sealed trait on[P] extends On.Fallback[P], Run[P, from]
//    transparent inline def apply[P]: on[P] = ${ On[P] }
//
//  object remote extends Narrow, Select[Call], Call[Nothing, from], Gateway[Nothing]:
//    sealed trait remote[P] extends Call[P, from], Gateway[P]
//    def apply[P]: remote[P] = erased

  export On.Placed.apply as placed
  export Select.Run.apply as on
  transparent inline def on[P]: On.Fallback[P] & Run[P, from] = ${ On[P] }

  export Select.Call.apply as remote
  def remote[P]: Narrow & Call[P, from] & Gateway[P] = erased
}
