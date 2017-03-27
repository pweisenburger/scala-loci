package loci
package transmitter
package transmittable

import _root_.rescala.core.Struct
import _root_.rescala.core.Pulse
import _root_.rescala.core.Engine
import _root_.rescala.core.Turn
import _root_.rescala.reactives.Signal
import scala.language.higherKinds

protected[transmitter] trait SignalTransmittable {
  implicit def rescalaSignalTransmittable
      [Sig[T, ES <: Struct] <: Signal[T, ES], T, S, U, ES <: Struct](implicit
      engine: Engine[ES],
      transmittable: Transmittable[(T, String, Boolean), S, (U, String, Boolean)],
      serializable: Serializable[S]) = {
    type From = (T, String, Boolean)
    type To = (U, String, Boolean)

    new PushBasedTransmittable[Sig[T, ES], From, S, To, engine.Signal[U]] {
      final val ignoredValue = null.asInstanceOf[T]
      final val ignoredString = null.asInstanceOf[String]

      def send(value: Sig[T, ES], remote: RemoteRef, endpoint: Endpoint[From, To]) = {
        val signal =
          (value
            map { (_, ignoredString, false) }
            recover { case throwable => (ignoredValue, throwable.toString, false) }
            withDefault { (ignoredValue, ignoredString, true) })

        val observer = signal observe endpoint.send

        endpoint.closed notify { _ => observer.remove }

        signal.now
      }

      def receive(value: To, remote: RemoteRef, endpoint: Endpoint[From, To]) = {
        val signal = engine.transaction() { _ => engine.Var.empty[U] }

        def update(signal: engine.Var[U], value: To) = value match {
          case (value, `ignoredString`, false) =>
            signal set value
          case (_, message, false) =>
            engine.transaction(signal) { implicit turn =>
              signal admitPulse Pulse.Exceptional(
                new rescala.RemoteReactiveFailure(message))
            }
          case _  =>
            signal.setEmpty
        }

        endpoint.closed notify { _ =>
          signal.setEmpty
          signal.disconnect
        }

        update(signal, value)
        endpoint.receive notify { update(signal, _) }

        signal
      }
    }
  }
}
