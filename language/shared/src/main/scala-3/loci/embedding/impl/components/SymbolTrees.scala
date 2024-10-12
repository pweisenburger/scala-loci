package loci
package embedding
package impl
package components

import scala.annotation.experimental
import scala.collection.mutable
import scala.util.control.NonFatal

object SymbolTrees:
  private val originalTreeCache = mutable.Map.empty[Any, Any]
  private val preprocessedTreeCache = mutable.Map.empty[Any, Any]

@experimental
trait SymbolTrees:
  this: Component =>
  import quotes.reflect.*

  private val originalTreeCache = SymbolTrees.originalTreeCache match
    case cache: mutable.Map[Symbol, Option[Tree]] @unchecked => cache
  private val preprocessedTreeCache = SymbolTrees.preprocessedTreeCache match
    case cache: mutable.Map[Symbol, Tree] @unchecked => cache

  private val currentCompilationUnit =
    try
      val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
      val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
      val ctx = quotesImplClass.getMethod("ctx")
      val compilationUnit = contextClass.getMethod("compilationUnit")
      () =>
        try Some(compilationUnit.invoke(ctx.invoke(quotes)))
        catch case NonFatal(_) => None
    catch case NonFatal(_) => () => None

  private val allCompilationUnits =
    try
      val quotesImplClass = Class.forName("scala.quoted.runtime.impl.QuotesImpl")
      val contextClass = Class.forName("dotty.tools.dotc.core.Contexts$Context")
      val runClass = Class.forName("dotty.tools.dotc.Run")
      val ctx = quotesImplClass.getMethod("ctx")
      val run = contextClass.getMethod("run")
      val units = runClass.getMethod("units")
      () =>
        try
          units.invoke(run.invoke(ctx.invoke(quotes))) match
            case compilationUnits: List[?] => Some(compilationUnits)
            case _ => None
        catch case NonFatal(_) => None
    catch case NonFatal(_) => () => None

  private val compilationUnitTypedTree =
    try
      val treeClass = Class.forName("dotty.tools.dotc.ast.Trees$Tree")
      val compilationUnitClass = Class.forName("dotty.tools.dotc.CompilationUnit")
      val tpdTree = compilationUnitClass.getMethod("tpdTree")
      (compilationUnit: Any) =>
        try
          tpdTree.invoke(compilationUnit) match
            case tree: Tree @unchecked if treeClass.isInstance(tree) => Some(tree)
            case _ => None
        catch case NonFatal(_) => None
    catch case NonFatal(_) => (compilationUnit: Any) => None

  private class DefinitionTreeFinder(symbol: Symbol) extends TreeAccumulator[Option[Definition]]:
    def ancestors(symbol: Symbol): Set[Symbol] =
      if symbol.exists then
        ancestors(symbol.maybeOwner) + symbol + symbol.moduleClass + symbol.companionClass + symbol.companionModule
      else
        Set.empty

    val owners = ancestors(symbol) - Symbol.noSymbol

    def foldTree(result: Option[Definition], tree: Tree)(owner: Symbol) =
      result orElse:
        tree match
          case _ if !(owners contains owner) => None
          case tree: Definition if tree.symbol == symbol => Some(tree)
          case tree @ (_: Definition | _: PackageClause) if !(owners contains tree.symbol) => None
          case _ => foldOverTree(result, tree)(owner)
  end DefinitionTreeFinder

  object symbolOriginalTree:
    def apply(symbol: Symbol) =
      originalTreeCache.getOrElseUpdate(symbol, {
        val compilationUnits =
          currentCompilationUnit().fold(allCompilationUnits()): compilationUnit =>
            allCompilationUnits().fold(Some(List(compilationUnit))): allCompilationUnits =>
              Some(compilationUnit :: (allCompilationUnits filterNot { _ == compilationUnit }))

        val tree =
          compilationUnits flatMap: compilationUnits =>
            compilationUnits collectFirst Function.unlift: compilationUnit =>
              compilationUnitTypedTree(compilationUnit) flatMap: tree =>
                DefinitionTreeFinder(symbol).foldTree(None, tree)(tree.symbol)

        tree orElse:
          try
            val tree = symbol.tree
            val pos = tree.pos
            Option.when(pos.start >= 0 && pos.end > pos.start && !(pos.toString endsWith ">")) { tree }
          catch
            case NonFatal(_) => None
      })

    def update(symbol: Symbol, tree: Tree) =
      originalTreeCache += symbol -> Some(tree)
  end symbolOriginalTree

  object symbolPreprocessedTree:
    def apply(symbol: Symbol) =
      preprocessedTreeCache.get(symbol)

    def update(symbol: Symbol, tree: Tree) =
      preprocessedTreeCache += symbol -> tree
  end symbolPreprocessedTree
end SymbolTrees
