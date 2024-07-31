package loci
package embedding
package impl
package components

import scala.annotation.experimental
import scala.collection.mutable
import scala.util.control.NonFatal

object SymbolTrees:
  private val treeCache = mutable.Map.empty[Any, Any]
  private val originalTreeCache = mutable.Map.empty[Any, Any]

@experimental
trait SymbolTrees:
  this: Component =>
  import quotes.reflect.*

  private val treeCache = SymbolTrees.treeCache match
    case cache: mutable.Map[Symbol, Tree] @unchecked => cache
  private val originalTreeCache = SymbolTrees.originalTreeCache match
    case cache: mutable.Map[Symbol, Tree] @unchecked => cache

  object symbolTree:
    def apply(symbol: Symbol) =
      treeCache.get(symbol) orElse:
        try Some(symbol.tree)
        catch case NonFatal(_) => None

    def update(symbol: Symbol, tree: Tree) =
      treeCache += symbol -> tree
  end symbolTree

  object symbolOriginalTree:
    def apply(symbol: Symbol) =
      originalTreeCache.get(symbol)

    def update(symbol: Symbol, tree: Tree) =
      originalTreeCache += symbol -> tree
  end symbolOriginalTree
end SymbolTrees
