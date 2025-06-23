package loci
package utility

import scala.quoted.*

object DummyImplicit:
  sealed trait Resolvable

  object Resolvable:
    final class Resolved[+T]
    transparent inline given Resolved[Any] = Resolved[Resolved[?]]

    object instance extends Resolvable
    transparent inline given [T](using inline res: Resolved[T], inline eq: T <:< Resolved[?]): Resolvable = instance

  sealed trait Unresolvable

  object Unresolvable:
    transparent inline given Unresolvable = ${ skip }
    def skip(using Quotes) = quotes.reflect.report.errorAndAbort("`Unresolvable` must not be constructed")
