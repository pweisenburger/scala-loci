package loci
package embedding
package impl

import scala.collection.mutable
import scala.quoted.*

object SourceCode:
  private val cache = mutable.WeakHashMap.empty[AnyRef, SourceCode]

  def apply(using Quotes)(file: quotes.reflect.SourceFile): SourceCode =
    cache.getOrElseUpdate(file, SourceCode(file.content getOrElse ""))
end SourceCode

case class SourceCode(content: String):
  def forwardSkipToCode(start: Int): Int =
    val length = noncommented.length
    var i = if start < 0 then 0 else if start >= length then length else start
    while i < length do
      val ch = noncommented(i)
      if ch != ' ' && ch != '\r' && ch != '\n' then
        return i
      i += 1
    i

  def backwardSkipToCode(start: Int): Int =
    val length = noncommented.length
    var i = if start < 0 then -1 else if start >= length then length - 1 else start
    while i >= 0 do
      val ch = noncommented(i)
      if ch != ' ' && ch != '\r' && ch != '\n' then
        return i
      i -= 1
    i

  def forwardSkipToLastCodeInLine(start: Int): Int =
    val length = noncommented.length
    var i = if start < 0 then 0 else if start >= length then length else start
    var j = i
    while i < length do
      val ch = noncommented(i)
      if ch == '\r' || ch == '\n' then
        return j
      if ch != ' ' then
        j = i
      i += 1
    start

  def backwardSkipToLastCodeInLine(start: Int): Int =
    val length = noncommented.length
    var i = if start < 0 then -1 else if start >= length then length - 1 else start
    var j = i
    while i >= 0 do
      val ch = noncommented(i)
      if ch == '\r' || ch == '\n' then
        return j
      if ch != ' ' then
        j = i
      i -= 1
    start

  private val noncommented =
    enum State:
      case
        Code, Brace, Identifier, IdentifierMaybeOperator, IdentifierOperator, Backquote,
        SingleLineString, SingleLineInterpolatedString, MultiLineString, MultiLineInterpolatedString,
        SingleLineComment, MultiLineComment

    import State.*

    extension (inline st: State)
      inline def isIdentifier = st == Identifier || st == IdentifierMaybeOperator || st == IdentifierOperator
      inline def isComment = st == SingleLineComment || st == MultiLineComment
      inline def isSingleLineString = st == SingleLineString || st == SingleLineInterpolatedString
      inline def isMultiLineString = st == MultiLineString || st == MultiLineInterpolatedString
      inline def isInterpolatedString = st == SingleLineInterpolatedString || st == MultiLineInterpolatedString

    val state = mutable.Stack.empty[State]
    state.push(Code)

    val length = content.length
    val builder = StringBuilder(length)
    var i = 0

    def handleSurrogate(check: Int => Boolean): Boolean =
      val ch = content(i)
      if check(ch.toInt) then
        return true
      if i + 1 < length && Character.isHighSurrogate(ch) && Character.isLowSurrogate(content(i + 1)) then
        val cp = Character.toCodePoint(ch, content(i + 1))
        if Character.isValidCodePoint(cp) && check(cp) then
          builder += ch
          i += 1
          return true
      false

    def special(cp: Int) =
      val chType = Character.getType(cp).toByte
      chType == Character.MATH_SYMBOL.toInt || chType == Character.OTHER_SYMBOL.toInt

    while i < length do
      val ch = content(i)
      val st = state.top

      inline def identifierStart() =
        ch >= 'a' && ch <= 'z' ||
        ch >= 'A' && ch <= 'Z' ||
        ch == '$' || ch == '_' || handleSurrogate(Character.isUnicodeIdentifierStart)

      inline def identifierRest() =
        ch >= 'a' && ch <= 'z' ||
        ch >= 'A' && ch <= 'Z' ||
        ch >= '0' && ch <= '1' ||
        ch == '$' || ch == '_' || (ch != '\u001A' && handleSurrogate(Character.isUnicodeIdentifierPart))

      inline def operatorRest() = ch match
        case '~' | '!' | '@' | '#' | '%' | '^' | '*' | '+' | '-' | '<' | '>' | '?' | ':' | '=' | '&' | '|' | '\\' =>
          true
        case '/' =>
          i + 1 >= length || (content(i + 1) != '/' && content(i + 1) != '*')
        case _ =>
          handleSurrogate(special)

      st match
        case Code | Brace | Identifier | IdentifierMaybeOperator | IdentifierOperator | MultiLineComment =>
          if st != MultiLineComment then
            st match
              case Identifier =>
                if ch == '_' then
                  state.pop()
                  state.push(IdentifierMaybeOperator)
                else if !identifierRest() then
                  state.pop()
              case IdentifierMaybeOperator =>
                state.pop()
                if identifierRest() then
                  state.push(Identifier)
                else if operatorRest() then
                  state.push(IdentifierOperator)
              case IdentifierOperator =>
                if !operatorRest() then
                  state.pop()
              case _ =>
                if identifierStart() then
                  state.push(Identifier)
            end match
          end if

          if i + 1 < length && ch == '/' && content(i + 1) == '*' then
            builder += ' '
            i += 1
            state.push(MultiLineComment)
          else if i + 1 < length && ch == '*' && content(i + 1) == '/' then
            builder += ' '
            i += 1
            if state.top == MultiLineComment then
              state.pop()
          else if state != MultiLineComment then
            if i + 1 < length && ch == '/' && content(i + 1) == '/' then
              state.push(SingleLineComment)
            else if i + 2 < length && ch == '"' && content(i + 1) == '"' && content(i + 2) == '"' then
              builder += '"' += '"'
              i += 2
              if st.isIdentifier then
                state.push(MultiLineInterpolatedString)
              else
                state.push(MultiLineString)
            else if ch == '"' then
              if st.isIdentifier then
                state.push(SingleLineInterpolatedString)
              else
                state.push(SingleLineString)
            else if ch == '`' then
              state.push(Backquote)
            else if state.top == Brace then
              if ch == '{' then
                state.push(Brace)
              else if ch == '}' then
                state.pop()

        case SingleLineComment =>
          if ch == '\r' || ch == '\n' then
            state.pop()

        case SingleLineString | SingleLineInterpolatedString | MultiLineString | MultiLineInterpolatedString =>
          if st.isSingleLineString then
            if ch == '"' || ch == '\r' || ch == '\n' then
              state.pop()
            else if i + 1 < length && ch == '\\' && content(i + 1) == '"' then
              builder += '\\'
              i += 1
          else if st.isMultiLineString then
            if i + 2 < length && ch == '"' && content(i + 1) == '"' && content(i + 2) == '"' then
              builder += '"' += '"'
              i += 2
              state.pop()

          if st.isInterpolatedString && ch == '$' && i + 1 < length then
            builder += '$'
            i += 1
            if content(i) == '{' then
              state.push(Brace)

        case Backquote =>
          if ch == '`' || ch == '\r' || ch == '\n' then
            state.pop()
      end match

      content(i) match
        case ch @ ('\r' | '\n') =>
          builder += ch
        case ch if Character.isWhitespace(ch) =>
          state.top match
            case Backquote | SingleLineString | SingleLineInterpolatedString | MultiLineString | MultiLineInterpolatedString =>
              builder += '\u2420'
            case _ =>
              if i > 0 && i + 1 < length && content(i - 1) == '\'' && content(i + 1) == '\'' &&
                 !st.isComment && !state.top.isComment then
                builder += '\u2420'
              else
                builder += ' '
        case ch if st.isComment || state.top.isComment =>
          builder += ' '
        case ch =>
          builder += ch

      // assert(state.nonEmpty)
      // assert((state.iterator count { st => st.isIdentifier }) <= 1)
      // assert(state.iterator find { st => st.isIdentifier } forall { _ == state.top })
      // assert(state.last == Code)

      i += 1
    end while

    // assert(builder.result().length == content.length)

    builder.result()
  end noncommented
end SourceCode
