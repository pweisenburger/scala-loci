package loci
package embedding
package impl

import utility.LiteralByte

import scala.collection.mutable
import scala.quoted.*

object SourceCode:
  private val cache = Cache[Any, SourceCode]

  def apply(using Quotes)(file: quotes.reflect.SourceFile): SourceCode =
    cache.getOrElseUpdate(file):
      SourceCode(file.content getOrElse "")
end SourceCode

case class SourceCode(code: String) extends IndexedSeq[Char]:
  def apply(i: Int): Char = code(i)

  def length: Int = code.length

  private inline def forwardStart(start: Int) =
    if start < 0 then 0 else if start >= length then length else start

  private inline def backwardStart(start: Int) =
    if start < 0 then -1 else if start >= length then length - 1 else start

  def forwardSkipToken(start: Int): Int =
    val length = structure.length
    val init = forwardStart(start)
    var i = init
    if i < length then
      structure(i) match
        case Item.OpenParen | Item.CloseParen | Item.OpenBracket | Item.CloseBracket | Item.OpenBrace | Item.CloseBrace |
             Item.At | Item.Dot | Item.Comma | Item.Colon | Item.Semicolon =>
          return i + 1
        case _ =>
    while i < length do
      val item = structure(i)
      if item != Item.Identifier && item != Item.Operator && item != Item.Underscore && item != Item.String then
        return i
      if i > init then
        val prev = structure(i - 1)
        if item == Item.Operator && prev != Item.Operator && prev != Item.Underscore then
          return i
        if item != Item.Operator && prev == Item.Operator then
          return i
      i += 1
    i

  def backwardSkipToken(start: Int): Int =
    val init = backwardStart(start)
    var i = init
    if i >= 0 then
      structure(i) match
        case Item.OpenParen | Item.CloseParen | Item.OpenBracket | Item.CloseBracket | Item.OpenBrace | Item.CloseBrace |
             Item.At | Item.Dot | Item.Comma | Item.Colon | Item.Semicolon =>
          return i - 1
        case _ =>
    while i >= 0 do
      val item = structure(i)
      if item != Item.Identifier && item != Item.Operator && item != Item.Underscore && item != Item.String then
        return i
      if i < init then
        val prev = structure(i + 1)
        if prev == Item.Operator && item != Item.Operator && item != Item.Underscore then
          return i
        if prev != Item.Operator && item == Item.Operator then
          return i
      i -= 1
    i

  def forwardSkipToToken(start: Int): Int =
    val length = structure.length
    var i = forwardStart(start)
    while i < length do
      val item = structure(i)
      if item != Item.Whitespace && item != Item.LineBreak then
        return i
      i += 1
    i

  def backwardSkipToToken(start: Int): Int =
    var i = backwardStart(start)
    while i >= 0 do
      val item = structure(i)
      if item != Item.Whitespace && item != Item.LineBreak then
        return i
      i -= 1
    i

  def forwardSkipToLastTokenInLine(start: Int): Int =
    val length = structure.length
    var i = forwardStart(start)
    var j = i
    while i < length do
      val item = structure(i)
      if item == Item.LineBreak then
        return j
      if item != Item.Whitespace then
        j = i
      i += 1
    start

  def backwardSkipToLastTokenInLine(start: Int): Int =
    var i = backwardStart(start)
    var j = i
    while i >= 0 do
      val item = structure(i)
      if item == Item.LineBreak then
        return j
      if item != Item.Whitespace then
        j = i
      i -= 1
    start

  def forwardSkipToMatchingBracket(start: Int): Int =
    val length = structure.length
    var i = forwardStart(start)
    var level = 0
    val (open, close) = structure(i) match
      case Item.OpenParen => Item.OpenParen -> Item.CloseParen
      case Item.OpenBracket => Item.OpenBracket -> Item.CloseBracket
      case Item.OpenBrace => Item.OpenBrace -> Item.CloseBrace
      case _ => return i
    while i < length do
      val item = structure(i)
      if item == open then
        level += 1
      else if item  == close then
        level -= 1
        if level == 0 then
          return i
      i += 1
    i

  def backwardSkipToMatchingBracket(start: Int): Int =
    var i = backwardStart(start)
    var level = 0
    val (open, close) = structure(i) match
      case Item.CloseParen => Item.OpenParen -> Item.CloseParen
      case Item.CloseBracket => Item.OpenBracket -> Item.CloseBracket
      case Item.CloseBrace => Item.OpenBrace -> Item.CloseBrace
      case _ => return i
    while i >= 0 do
      val item = structure(i)
      if item == close then
        level += 1
      else if item  == open then
        level -= 1
        if level == 0 then
          return i
      i -= 1
    i

  private type Item = Byte

  private object Item:
    inline val Whitespace = LiteralByte(' ')
    inline val LineBreak = LiteralByte('\n')
    inline val String = LiteralByte('"')
    inline val Identifier = LiteralByte('i')
    inline val Operator = LiteralByte('!')
    inline val Underscore = LiteralByte('_')
    inline val OpenParen = LiteralByte('(')
    inline val CloseParen = LiteralByte(')')
    inline val OpenBracket = LiteralByte('[')
    inline val CloseBracket = LiteralByte(']')
    inline val OpenBrace = LiteralByte('{')
    inline val CloseBrace = LiteralByte('}')
    inline val At = LiteralByte('@')
    inline val Dot = LiteralByte('.')
    inline val Comma = LiteralByte(',')
    inline val Colon = LiteralByte(':')
    inline val Semicolon = LiteralByte(';')

  private val structure =
    enum State:
      case
        Code, Brace, Identifier, IdentifierMaybeOperator, IdentifierOperator, Backquote,
        SingleCharacterString, SingleLineString, SingleLineInterpolatedString, MultiLineString, MultiLineInterpolatedString,
        SingleLineComment, MultiLineComment

    import State.*

    extension (inline st: State)
      inline def isIdentifier = st == Identifier || st == IdentifierMaybeOperator || st == IdentifierOperator
      inline def isComment = st == SingleLineComment || st == MultiLineComment
      inline def isSingleLineString = st == SingleLineString || st == SingleLineInterpolatedString
      inline def isMultiLineString = st == MultiLineString || st == MultiLineInterpolatedString
      inline def isInterpolatedString = st == SingleLineInterpolatedString || st == MultiLineInterpolatedString
      inline def isString = st.isSingleLineString || st.isMultiLineString || st == SingleCharacterString

    val state = mutable.Stack.empty[State]
    state.push(Code)

    val length = code.length
    val structure = Array.ofDim[Item](length)
    var i = 0
    var k = 0

    inline def advance(item: Item) =
      structure(k) = item
      k += 1
      i += 1

    def handleSurrogate(check: Int => Boolean, item: Item): Boolean =
      val ch = code(i)
      if check(ch.toInt) then
        return true
      if i + 1 < length && Character.isHighSurrogate(ch) && Character.isLowSurrogate(code(i + 1)) then
        val cp = Character.toCodePoint(ch, code(i + 1))
        if Character.isValidCodePoint(cp) && check(cp) then
          advance(item)
          return true
      false

    def special(cp: Int) =
      val chType = Character.getType(cp).toByte
      chType == Character.MATH_SYMBOL.toInt || chType == Character.OTHER_SYMBOL.toInt

    while i < length do
      val ch = code(i)
      val st = state.top

      inline def identifierStart() =
        ch >= 'a' && ch <= 'z' ||
        ch >= 'A' && ch <= 'Z' ||
        ch == '$' || ch == '_' || handleSurrogate(Character.isUnicodeIdentifierStart, Item.Identifier)

      inline def identifierRest() =
        ch >= 'a' && ch <= 'z' ||
        ch >= 'A' && ch <= 'Z' ||
        ch >= '0' && ch <= '1' ||
        ch == '$' || ch == '_' || (ch != '\u001A' && handleSurrogate(Character.isUnicodeIdentifierPart, Item.Identifier))

      inline def operatorRest() =
        operatorCharacter(ch) || handleSurrogate(special, Item.Operator)

      inline def operatorCharacter(ch: Char) = ch match
        case '~' | '!' | '@' | '#' | '%' | '^' | '*' | '+' | '-' | '<' | '>' | '?' | ':' | '=' | '&' | '|' | '\\' =>
          true
        case '/' =>
          i + 1 >= length || (code(i + 1) != '/' && code(i + 1) != '*')
        case _ =>
          false

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

          if i + 1 < length && ch == '/' && code(i + 1) == '*' then
            advance(Item.Whitespace)
            state.push(MultiLineComment)
          else if i + 1 < length && ch == '*' && code(i + 1) == '/' then
            advance(Item.Whitespace)
            if st == MultiLineComment then
              state.pop()
          else if st != MultiLineComment then
            if i + 1 < length && ch == '/' && code(i + 1) == '/' then
              state.push(SingleLineComment)
            else if i + 1 < length && ch == '\'' && code(i + 1) == '\\' then
              state.push(SingleCharacterString)
            else if i + 2 < length && ch == '\'' && code(i + 2) == '\'' then
              state.push(SingleCharacterString)
            else if i + 2 < length && ch == '"' && code(i + 1) == '"' && code(i + 2) == '"' then
              advance(Item.String)
              advance(Item.String)
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

        case SingleCharacterString =>
          if ch == '\'' then
            state.pop()
          else if i + 1 < length && ch == '\\' && code(i + 1) == '\'' then
            advance(Item.String)

        case SingleLineString | SingleLineInterpolatedString | MultiLineString | MultiLineInterpolatedString =>
          if st.isSingleLineString then
            if ch == '"' then
              state.pop()
            else if i + 1 < length && ch == '\\' && code(i + 1) == '"' then
              advance(Item.String)
          else if st.isMultiLineString then
            if i + 2 < length && ch == '"' && code(i + 1) == '"' && code(i + 2) == '"' then
              advance(Item.String)
              advance(Item.String)
              state.pop()

          if st.isInterpolatedString && ch == '$' && i + 1 < length then
            advance(Item.String)
            if code(i) == '{' then
              state.push(Brace)

        case Backquote =>
          if ch == '`' then
            state.pop()
      end match

      if st == Backquote || state.top == Backquote then
        advance(Item.Identifier)
      else if st.isString || state.top.isString then
        advance(Item.String)
      else if st.isComment || state.top.isComment then
        if code(i) == '\r' || code(i) == '\n' then
          advance(Item.LineBreak)
        else
          advance(Item.Whitespace)
      else
        code(i) match
          case '\r' | '\n' => advance(Item.LineBreak)
          case '(' => advance(Item.OpenParen)
          case ')' => advance(Item.CloseParen)
          case '[' => advance(Item.OpenBracket)
          case ']' => advance(Item.CloseBracket)
          case '{' => advance(Item.OpenBrace)
          case '}' => advance(Item.CloseBrace)
          case '_' => advance(Item.Underscore)
          case '.' => advance(Item.Dot)
          case ',' => advance(Item.Comma)
          case ';' => advance(Item.Semicolon)
          case ch @ (':' | '@') =>
            if i > 0 && (operatorCharacter(code(i - 1)) || code(i - 1) == '_') || i < length && operatorCharacter(code(i + 1)) then
              advance(Item.Operator)
            else if ch == ':' then
              advance(Item.Colon)
            else if ch == '@' then
              advance(Item.At)
          case ch =>
            if Character.isWhitespace(ch) then
              advance(Item.Whitespace)
            else if k > 0 && structure(k - 1) == Item.Operator && Character.isLowSurrogate(ch) || operatorCharacter(ch) then
              advance(Item.Operator)
            else
              advance(Item.Identifier)

      // assert(i == k)
      // assert(state.nonEmpty)
      // assert((state.iterator count { st => st.isIdentifier }) <= 1)
      // assert(state.iterator find { st => st.isIdentifier } forall { _ == state.top })
      // assert(state.last == Code)
    end while

    structure
  end structure
end SourceCode
