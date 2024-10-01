package loci
package embedding
package impl
package components

import scala.annotation.experimental

@experimental
trait ErrorReporter:
  this: Component =>
  import quotes.reflect.*

  private var enabled = true

  private var errors = List.empty[(String, Position)]

  private def reporting  =
    val reversed = errors.reverse
    val filtered = reversed filterNot { (_, pos) => pos == Position.ofMacroExpansion }
    if filtered.nonEmpty then filtered else reversed

  def errorAndCancel(msg: String, pos: Position): Unit =
    if enabled then
      errors ::= (msg, pos)

  def reportErrors(abortOnErrors: Boolean) =
    if abortOnErrors then
      reporting match
        case init :+ (message, pos) =>
          init foreach { report.error(_, _) }
          report.errorAndAbort(message, pos)
        case _ =>
    else
      reporting foreach { report.error(_, _) }

  def canceled = errors.nonEmpty

  def enableErrorAndCancel() = enabled = true

  def disableErrorAndCancel() = enabled = false

  def ErrorAndCancelEnabled = enabled
end ErrorReporter
