package loci
package language

import loci.embedding.*

import scala.annotation.experimental

extension [_placed_[T, P] <: T placed P, TU, PU](inline placed: TU _placed_ PU)
  @experimental
  transparent inline infix def and[TV, TR, PV, PR](inline v: TV _placed_ PV)(using
      LowestCommonSuperType[TU, TV, TR],
      LowestCommonSuperType[PU, PV, PR]): TR on PR =
    ${ embedding.impl.inferrableCanonicalPlacementTypeContextClosure[TR on PR]('placed, 'v) }
