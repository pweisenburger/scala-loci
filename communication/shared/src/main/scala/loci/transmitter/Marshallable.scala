package loci
package transmitter

import scala.annotation.implicitNotFound
import scala.concurrent.Future
import scala.util.control.NonFatal
import scala.util.{Success, Try}

@implicitNotFound("${B} is not marshallable")
sealed trait Marshallable[-B, +R, +P] {
  def marshal(value: B, abstraction: AbstractionRef): MessageBuffer
  def unmarshal(value: MessageBuffer, abstraction: AbstractionRef): Try[R]
  def unmarshal(value: Notice.Steady[Try[MessageBuffer]], abstraction: AbstractionRef): P
  def connected: Boolean
}

object Marshallable {
  @inline def apply[T](implicit resolution: Resolution[T, _, _]): resolution.Type = resolution.self

  @inline def Argument[T](implicit resolution: Resolution[T, T, _]): resolution.Type = resolution.self

  @implicitNotFound("${B} is not marshallable")
  sealed trait Resolution[B, R, P] extends Marshallable[B, R, P] {
    type Type = Marshallable[B, R, P]
    @inline def self: Type = this
  }

  object Resolution {
    implicit object nothing extends Resolution[Nothing, Nothing, Future[Nothing]] {
      def nothing = throw new RemoteAccessException("Unexpected value of bottom type")
      def marshal(value: Nothing, abstraction: AbstractionRef) =
        nothing
      def unmarshal(value: MessageBuffer, abstraction: AbstractionRef) =
        nothing
      def unmarshal(value: Notice.Steady[Try[MessageBuffer]], abstraction: AbstractionRef) =
        (value map { _ map { _ => nothing } }).toFutureFromTry
      def connected = false
    }

    implicit object `null` extends Resolution[Null, Null, Future[Null]] {
      def marshal(value: Null, abstraction: AbstractionRef) =
        MessageBuffer.empty
      def unmarshal(value: MessageBuffer, abstraction: AbstractionRef) =
        Success(null)
      def unmarshal(value: Notice.Steady[Try[MessageBuffer]], abstraction: AbstractionRef) =
        (value map { _ map { _ => null } }).toFutureFromTry
      def connected = false
    }

    implicit object unit extends Resolution[Unit, Unit, Future[Unit]] {
      def marshal(value: Unit, abstraction: AbstractionRef) =
        MessageBuffer.empty
      def unmarshal(value: MessageBuffer, abstraction: AbstractionRef) =
        Success(())
      def unmarshal(value: Notice.Steady[Try[MessageBuffer]], abstraction: AbstractionRef) =
        (value map { _ map { _ => () } }).toFutureFromTry
      def connected = false
    }

    implicit def marshallable[B, I, R, P, T <: Transmittables](implicit
        resolution: Transmittable.Resolution[B, I, R, P, T],
        serializer: Serializable[I],
        contextBuilder: ContextBuilder[T]): Marshallable.Resolution[B, R, P] =
      new Marshallable.Resolution[B, R, P] {
        val transmittable = resolution.transmittable

        def connected = (transmittable: Transmittable.Any[B, I, R]) match {
          case _: ConnectedTransmittable[_, _, _] => true
          case _: ConnectedTransmittable.Proxy[_, _, _] => true
          case _ => false
        }

        def marshal(value: B, abstraction: AbstractionRef) =
          try {
            implicit val context = contextBuilder(
              transmittable.transmittables, abstraction, ContextBuilder.sending)
            serializer serialize (transmittable buildIntermediate value)
          }
          catch {
            case NonFatal(exception) =>
              throw new RemoteAccessException(s"marshalling failed: $value").initCause(exception)
          }

        def unmarshal(value: MessageBuffer, abstraction: AbstractionRef) =
          try {
            implicit val context = contextBuilder(
              transmittable.transmittables, abstraction, ContextBuilder.receiving)
            serializer deserialize value map transmittable.buildResult
          }
          catch {
            case NonFatal(exception) =>
              throw new RemoteAccessException(s"unmarshalling failed: $value").initCause(exception)
          }

        def unmarshal(value: Notice.Steady[Try[MessageBuffer]], abstraction: AbstractionRef) =
          try {
            implicit val context = contextBuilder(
              transmittable.transmittables, abstraction, ContextBuilder.receiving)
            transmittable buildProxy (
              value map { _ flatMap serializer.deserialize })
          }
          catch {
            case NonFatal(exception) =>
              throw new RemoteAccessException("unmarshalling failed: could not create proxy object").initCause(exception)
          }
      }
  }
}
