package loci
package embedding
package impl
package components

import scala.annotation.experimental

@experimental
trait AccessNotation:
  this: Component =>
  import quotes.reflect.*

  def notationPositionCheck(pos: Position, infix: Boolean, applied: Boolean): (Option[String], Option[Position]) =
    val code = SourceCode(pos.sourceFile)
    var start = pos.end - 1
    var end = start

    val application =
      if end >= 0 && end < code.length && code(end) == ']' then
        start = code.backwardSkipToMatchingBracket(end) - 1
        Some(code.view.slice(start + 2, end).mkString)
      else
        None

    end = start
    start = code.backwardSkipToken(start)
    val token = code.view.slice(start + 1, end + 1).mkString
    if token == "apply" || token == "`apply`" then
      return (application, Some(Position(pos.sourceFile, start + 1, end + 1)))

    start = code.backwardSkipToToken(start)
    if infix && start >= 0 && code(start) == '.' then
      return (application, Some(Position(pos.sourceFile, start, start)))

    start = code.forwardSkipToToken(end + 1)
    if !applied && start < code.length && code(start) == '[' then
      end = code.forwardSkipToMatchingBracket(start)
      return (application, Some(Position(pos.sourceFile, start, end + 1)))

    (application, None)
  end notationPositionCheck

  def notationCheck(typeApply: TypeApply, infix: Boolean): Option[Position] =
    val (_, pos) = notationPositionCheck(typeApply.fun.pos, infix, applied = false)
    pos

  def notationPosition(apply: Apply): Position =
    val code = SourceCode(apply.fun.pos.sourceFile)
    val start = code.backwardSkipToken(apply.fun.pos.end - 1) + 1
    val end = code.forwardSkipToMatchingBracket(code.forwardSkipToToken(apply.fun.pos.end))
    if end < code.length && code(end) == ')' then
      Position(apply.fun.pos.sourceFile, start, end + 1)
    else
      Position(apply.fun.pos.sourceFile, start, apply.fun.pos.end)

  def argNotation(arg: Tree): String =
    arg.pos.sourceCode filterNot { _ exists Character.isWhitespace } getOrElse "..."

  def argsNotation(args: List[Tree]): String =
    if args.sizeIs == 1 then argNotation(args.head) else "..."
end AccessNotation
