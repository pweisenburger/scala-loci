package loci
package runtime

import embedding.*

import scala.annotation.unchecked.uncheckedVariance

object RemoteValue {
  private sealed trait Impl[+P, +T] extends PlacedValue[P @uncheckedVariance, T]
  private val implementation: Impl[Nothing, Nothing] = new Impl[Nothing, Nothing] { }
  inline def apply[P, T](): PlacedValue[P, T] = implementation: Impl[P, T]
}
