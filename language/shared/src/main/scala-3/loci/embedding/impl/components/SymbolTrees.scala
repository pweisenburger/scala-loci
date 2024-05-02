package loci
package embedding
package impl
package components

import scala.annotation.experimental
import scala.collection.mutable
import scala.util.control.NonFatal

object SymbolTrees:
  private val cache = mutable.Map.empty[Any, Any]

@experimental
trait SymbolTrees:
  this: Component =>
  import quotes.reflect.*

  private val cache = SymbolTrees.cache match
    case cache: mutable.Map[Symbol, Tree] @unchecked => cache

  object symbolTree:
    def apply(symbol: Symbol) =
      cache.get(symbol) orElse:
        try Some(symbol.tree)
        catch case NonFatal(_) => None

    def update(symbol: Symbol, tree: Tree) =
      cache += symbol -> tree
  end symbolTree
end SymbolTrees
