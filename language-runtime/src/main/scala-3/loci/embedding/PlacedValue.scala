package loci
package embedding

import loci.language.{on as _, *}

import scala.annotation.unchecked.uncheckedVariance

abstract class PlacedValue[-P, +T] private[loci]:
  private[PlacedValue] type on = P @uncheckedVariance
//  extends Dynamic:
//  def selectDynamic(key: String): Unit = macro AccessorResolutionFailure.selectDynamic
//  def updateDynamic(key: String)(value: Any): Unit = macro AccessorResolutionFailure.updateDynamic
//  def applyDynamic(key: String)(args: Any*): Unit = macro AccessorResolutionFailure.applyDynamic
//  def applyDynamicNamed(key: String)(args: Any*): Unit = macro AccessorResolutionFailure.applyDynamic

object PlacedValue extends transmitter.RemoteAccessor.Default:
  type Resolution[P, T] = PlacedValue[P, T] { type on = P }

sealed trait Placed[-P, +T] extends PlacedValue[P, T]:
  infix def to[R, U](r: Remote[R])(using Subjectivity[T, U]): U
  def from[R]: T @uncheckedVariance from R
  infix def from[R](r: Remote[R]): T @uncheckedVariance fromSingle R
  infix def from[R](r: Seq[Remote[R]]): T @uncheckedVariance fromMultiple R
  infix def from[R](r0: Remote[R], r1: Remote[R], rn: Remote[R]*): T @uncheckedVariance fromMultiple R

object Placed:
  inline given lift[L, T, U](using Placement.Context.Resolution[L], PlacedClean[T, T, U]): Conversion[T, U on L] with
    transparent inline def apply(v: T) = erased(v): U on L

  trait Subjective[-P, +T]:
    protected def apply(v: Remote[P]): T

  object Selected:
    type Single[T]
    type Multiple[T]

  object Selection:
    type Single[P, T] = PlacedValue[P, Selected.Single[T]] { type on = P }
    type Multiple[P, T] = PlacedValue[P, Selected.Multiple[T]] { type on = P }
end Placed
