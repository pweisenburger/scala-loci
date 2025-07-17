package loci

import utility.reflectionExtensions.*

import org.scalatest.exceptions.TestFailedException
import org.scalactic.source

import scala.annotation.compileTimeOnly
import scala.quoted.*

object CompileTimeUtils:
  inline def assertType[T](inline value: Any): Unit =
    ${ assertTypeVariantsImpl[T, Nothing]('value, exact = false) }

  inline def assertType[T, U]: Unit =
    ${ assertTypeVariantsImpl[T, U](null, exact = false) }

  inline def assertExactType[T](inline value: Any): Unit =
    ${ assertTypeVariantsImpl[T, Nothing]('value, exact = true) }

  inline def assertExactType[T, U]: Unit =
    ${ assertTypeVariantsImpl[T, U](null, exact = true) }

  def assertTypeVariantsImpl[T: Type, U: Type](value: Expr[Any] | Null, exact: Boolean)(using Quotes): Expr[Unit] =
    import quotes.reflect.*

    object normalizer extends TypeMap(quotes):
      override def transform(tpe: TypeRepr) =
        val maybeExactType = if exact then tpe else tpe.dealias
        maybeExactType match
          case tpe: TypeRef => TypeIdent(tpe.typeSymbol).tpe
          case tpe => super.transform(tpe)

    val tpe = if value != null then value.asTerm.tpe else TypeRepr.of[U]

    if normalizer.transform(TypeRepr.of[T]).show == normalizer.transform(tpe.widenTermRefByName).show then
      '{ () }
    else
      val (actualType, maybeExactType) =
        if exact then
          (if value != null then s"${value.asTerm.safeShow} has type of form" else "Actual type has form", "exact type")
        else
          (if value != null then s"${value.asTerm.safeShow} has type" else "Actual type is", "type")
      failTest(s"$actualType `${tpe.widenTermRefByName.safeShow}`; $maybeExactType `${TypeRepr.of[T].safeShow}` expected")
  end assertTypeVariantsImpl

  inline def assertNoFailedAssertion(inline expr: Any): Unit =
    ${ assertNoFailedAssertionImpl('expr) }

  def assertNoFailedAssertionImpl(expr: Expr[Any])(using Quotes): Expr[Unit] =
    import quotes.reflect.*

    val testFailedException = TypeRepr.of[TestFailedException]

    object failedAssertionsFinder extends TreeAccumulator[List[String]]:
      def foldTree(messages: List[String], tree: Tree)(owner: Symbol) = tree match
        case tree @ Apply(Select(New(_), _), args) if tree.tpe <:< testFailedException =>
           args match
             case Block(List(DefDef(_, _, _, Some(Apply(_, List(Literal(StringConstant(message))))))), Closure(_, _)) :: _ =>
               message :: messages
             case _ =>
               "Assertion in compiled code failed" :: messages
        case _ =>
          foldOverTree(messages, tree)(owner)

    (failedAssertionsFinder.foldTree(List.empty, expr.asTerm.underlyingArgument)(Symbol.spliceOwner).lastOption
      map failTest
      getOrElse '{ () })
  end assertNoFailedAssertionImpl

  inline def containsCompileTimeOnly(inline expr: Any): Boolean =
    ${ containsCompileTimeOnlyImpl('expr) }

  def containsCompileTimeOnlyImpl(expr: Expr[Any])(using Quotes): Expr[Boolean] =
    import quotes.reflect.*

    val compileTimeOnlyAnnotation = TypeRepr.of[compileTimeOnly]

    object compileTimeOnlyAnnotationFinder extends TreeAccumulator[Boolean]:
      def foldTree(compileTimeOnlyFound: Boolean, tree: Tree)(owner: Symbol) =
        compileTimeOnlyFound ||
        (tree.symbol.annotations exists { _.tpe <:< compileTimeOnlyAnnotation }) ||
        foldOverTree(false, tree)(owner)

    Expr(compileTimeOnlyAnnotationFinder.foldTree(false, expr.asTerm)(Symbol.spliceOwner))
  end containsCompileTimeOnlyImpl

  inline def containsValueOfType[T, U]: Boolean =
    ${ containsValueOfTypeImpl[T, U] }

  def containsValueOfTypeImpl[T: Type, U: Type](using Quotes): Expr[Boolean] =
    import quotes.reflect.*

    val symbol = TypeRepr.of[T].typeSymbol
    val tpe = TypeRepr.of[U]

    Expr(symbol.declaredFields ++ symbol.declaredMethods exists { Ref(_).tpe.finalResultType <:< tpe })
  end containsValueOfTypeImpl

  private def failTest(message: String)(using Quotes) =
    import quotes.reflect.*
    '{ throw new TestFailedException(_ => Some(${Expr(message)}), None, Left(source.Position.here), None, Vector.empty) }
end CompileTimeUtils
