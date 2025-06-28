package loci
package runtime

import transmitter.Parser._

import scala.util.Try

object Value {
  case class Signature(name: String, module: String, path: List[String]) {
    override def toString: String =
      if (path.isEmpty) s"$module: $name" else s"$module.${path mkString "."}: $name"
  }

  object Signature {
    def serialize(signature: Signature): String =
      elements(
        string(signature.name),
        string(signature.module),
        list(signature.path map string)).toString

    def deserialize(signature: String): Try[Signature] = Try {
      val Seq(name, module, path) = parse(signature).asElements(3): @unchecked
      Signature(
        name.asString,
        module.asString,
        path.asList map { _.asString })
    }
  }

  case class Reference(channelName: String, channelAnchor: String,
        remote: Remote.Reference, system: System)
      extends transmitter.AbstractionRef {
    lazy val channel: Channel = system.obtainChannel(channelName, channelAnchor, remote)
    def derive(name: String) = Reference(s"$channelName:$name", channelAnchor, remote, system)

    override def toString: String = s"[channel:$channelName]$remote"
  }
}
