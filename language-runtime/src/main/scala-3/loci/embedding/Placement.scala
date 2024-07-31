package loci
package embedding

import scala.annotation.{compileTimeOnly, implicitNotFound, nowarn}
import scala.annotation.unchecked.uncheckedVariance

infix type of[T <: Nothing, P] = T { type on = P }
@nowarn // use `with` instead of `&` for better IDE compatibility
infix type on[T, P] = Placed[P, T] with T
infix type placed[T, P] = Placed[P, T]
infix type from[T, R] = PlacedValue.Resolution[R, T]
infix type fromSingle[T, P] = Placed.Selection.Single[P, T]
infix type fromMultiple[T, P] = Placed.Selection.Multiple[P, T]

object Multitier:
  @implicitNotFound("Expression can only be used in a multitier module.")
  sealed trait Context

  object Context:
    @compileTimeOnly("Expression can only be used in a multitier module.")
    given fallback: Context = erased
  end Context

  sealed trait nonplaced
  infix type `type`[N >: nonplaced <: nonplaced, T] = Multitier.Context ?=> T
end Multitier

object Placement:
  @implicitNotFound("Expression must be placed on a peer.")
  sealed trait Context[+P]:
    private[Context] type Peer = P @uncheckedVariance

  object Context:
    type Resolution[P] = Context[P] { type Peer = P }

    @compileTimeOnly("Expression must be placed on a peer.")
    given fallback[P]: Resolution[P] = erased
  end Context
end Placement
