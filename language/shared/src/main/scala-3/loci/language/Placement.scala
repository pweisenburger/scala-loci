package loci

import communicator.*
import embedding.*
import messaging.*
import scala.annotation.{compileTimeOnly, experimental}

package object language:
  inline def connect[P](
      inline setup: Connector[ConnectionsBase.Protocol]): Connections =
    ${ impl.Connections.connect[P]('setup) }

  inline def connect[P](
      inline factory: ConnectionSetupFactory[ConnectionsBase.Protocol])(
      inline url: String,
      inline props: ConnectionSetupFactory.Properties = Map.empty): Connections =
    ${ impl.Connections.connect[P]('factory, 'url, 'props) }

  inline def listen[P](
      inline setup: Listener[ConnectionsBase.Protocol]): Connections =
    ${ impl.Connections.listen[P]('setup) }

  inline def listen[P](
      inline factory: ConnectionSetupFactory[ConnectionsBase.Protocol])(
      inline url: String,
      inline props: ConnectionSetupFactory.Properties = Map.empty): Connections =
    ${ impl.Connections.listen[P]('factory, 'url, 'props) }

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
