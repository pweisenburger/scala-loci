package loci
package embedding
package impl

import scala.collection.mutable

final class Cache[K, V]:
  private val cache = mutable.WeakHashMap.empty[K, V]

  def get(weakKey: K): Option[V] =
    cache.get(weakKey)

  def getOrElseUpdate(weakKey: K)(value: => V): V =
    cache.getOrElseUpdate(weakKey, value)

  def update(weakKey: K, value: V): Unit =
    cache.update(weakKey, value)

  def remove(weakKey: K): Option[V] =
    cache.remove(weakKey)
end Cache

object Cache:
  final class Tiered[K, V]:
    private val cache = Cache[K, (V, Int)]

    def get(weakKey: K): Option[V] =
      cache.get(weakKey) map { (value, _) => value }

    def getOrElseUpdate(weakKey: K, tier: Int)(value: => V): V =
      cache.get(weakKey) match
        case Some(value, valueTier) if valueTier >= tier =>
          value
        case _ =>
          val updatedValue = value
          cache.update(weakKey, updatedValue -> tier)
          updatedValue

    def update(weakKey: K, value: V, tier: Int): Unit =
      if cache.get(weakKey) forall { (_, valueTier) => valueTier <= tier } then
        cache.update(weakKey, value -> tier)

    def remove(weakKey: K): Option[V] =
      cache.remove(weakKey) map { (value, _) => value }
  end Tiered

  final class Layered[WK, SK, V]:
    private val cache = mutable.WeakHashMap.empty[WK, mutable.Map[SK, V]]

    def get(weakKey: WK, strongKey: SK): Option[V] =
      cache.get(weakKey) match
        case Some(cache) => cache.get(strongKey)
        case _ => None

    def getOrElseUpdate(weakKey: WK, strongKey: SK)(value: => V): V =
      cache.getOrElseUpdate(weakKey, mutable.Map.empty[SK, V]).getOrElseUpdate(strongKey, value)

    def update(weakKey: WK, strongKey: SK, value: V): Unit =
      cache.getOrElseUpdate(weakKey, mutable.Map.empty[SK, V]).update(strongKey, value)

    def remove(weakKey: WK, strongKey: SK): Option[V] =
      cache.get(weakKey) match
        case Some(cache) =>
          val removed = cache.remove(strongKey)
          if cache.isEmpty then this.cache.remove(weakKey)
          removed
        case _ =>
          None
  end Layered

  object Layered:
    final class Tiered[WK, SK, V]:
      private val cache = Layered[WK, SK, (V, Int)]

      def get(weakKey: WK, strongKey: SK): Option[V] =
        cache.get(weakKey, strongKey) map { (value, _) => value }

      def getOrElseUpdate(weakKey: WK, strongKey: SK, tier: Int)(value: => V): V =
        cache.get(weakKey, strongKey) match
          case Some(value, valueTier) if valueTier >= tier =>
            value
          case _ =>
            val updatedValue = value
            cache.update(weakKey, strongKey, updatedValue -> tier)
            updatedValue

      def update(weakKey: WK, strongKey: SK, value: V, tier: Int): Unit =
        if cache.get(weakKey, strongKey) forall { (_, valueTier) => valueTier <= tier } then
          cache.update(weakKey, strongKey, value -> tier)

      def remove(weakKey: WK, strongKey: SK): Option[V] =
        cache.remove(weakKey, strongKey) map { (value, _) => value }
    end Tiered
  end Layered
end Cache
