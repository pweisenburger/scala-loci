package loci
package utility

import scala.quoted.*

object LiteralByte:
  transparent inline def apply[T <: Byte | Short | Int | Long | Char](inline v: T): Byte =
    ${ LiteralByte.impl('v) }

  def impl[T <: Byte | Short | Int | Long | Char: Type](using Quotes)(v: Expr[T]): Expr[Byte] =
    import quotes.reflect.*

    val value =
      if v.isExprOf[Byte] then
        v.asExprOf[Byte].valueOrAbort
      else if v.isExprOf[Short] then
        v.asExprOf[Short].valueOrAbort.toByte
      else if v.isExprOf[Int] then
        v.asExprOf[Int].valueOrAbort.toByte
      else if v.isExprOf[Long] then
        v.asExprOf[Long].valueOrAbort.toByte
      else if v.isExprOf[Char] then
        v.asExprOf[Char].valueOrAbort.toByte
      else
        report.errorAndAbort("Unexpected non-numeric value.")

    Literal(ByteConstant(value)).asExprOf[Byte]
  end impl
end LiteralByte
