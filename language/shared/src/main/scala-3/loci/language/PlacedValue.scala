package loci
package language

import loci.embedding.*

import scala.annotation.experimental

extension [TU, PU](inline placed: TU on PU)
  @experimental
  transparent inline infix def and[TV, TR, PV, PR](inline v: TV on PV)(using
      LowestCommonSuperType[TU, TV, TR],
      LowestCommonSuperType[PU, PV, PR]): TR on PR =
    ${ embedding.impl.inferrableCanonicalPlacementTypeContextClosure[TR on PR]('placed, 'v) }
