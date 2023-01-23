package loci
package embedding
package impl

import scala.reflect.macros.blackbox

trait ContextReference {
  object Value {
    trait Base[C <: blackbox.Context] { val c: C }
  }

  type Value[C <: blackbox.Context] <: Value.Base[C]

  def apply[C <: blackbox.Context](c: C): Value[c.type]

  private var value: Value[_] = _

  final def get(c: blackbox.Context): Value[c.type] =
    this.value match {
      case value: Value[c.type] @unchecked if value.c eq c =>
        value
      case _ =>
        val value = apply(c)
        this.value = value
        value
    }
}
