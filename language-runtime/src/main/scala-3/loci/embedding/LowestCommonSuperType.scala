package loci
package embedding

import loci.language.*
import loci.utility.DummyImplicit


sealed trait LowestCommonSuperType[T, U, R]

sealed trait LowestCommonSuperTypeFallback:
  given[T, U, R]: LowestCommonSuperType[T, U, R] = erased

sealed trait LowestCommonSuperTypeDirect extends LowestCommonSuperTypeFallback:
  given[T, U, R](using CommonSuperType[T, U, R]): LowestCommonSuperType[T, U, R] = erased

sealed trait LowestCommonSuperTypeDeterminedResult extends LowestCommonSuperTypeDirect:
  given[T, U, V, R](using DummyImplicit.Resolvable, CommonSuperType[T, U, V])(using R =:= V): LowestCommonSuperType[T, U, R] = erased

sealed trait LowestCommonSuperTypeAny extends LowestCommonSuperTypeDeterminedResult:
  given[T]: LowestCommonSuperType[Any, T, Any] = erased

object LowestCommonSuperType extends LowestCommonSuperTypeAny:
  given[T]: LowestCommonSuperType[T, Any, Any] = erased


sealed trait CommonSuperType[-T, -U, R]

sealed trait CommonSuperTypeFallback:
  given[T, U, R]: CommonSuperType[T, U, R] = erased

sealed trait CommonSuperTypeDefault extends CommonSuperTypeFallback:
  given[T]: CommonSuperType[T, T, T] = erased

object CommonSuperType extends CommonSuperTypeDefault:
  given[T, _Local_[T] <: Local[T]]: CommonSuperType[_Local_[T], _Local_[T], _Local_[T]] = erased
