package loci
package embedding
package impl

import components.*

import scala.annotation.experimental
import scala.quoted.*

@experimental
object Multitier:
  def annotation(using Quotes)(tree: quotes.reflect.Definition): List[quotes.reflect.Definition] =
    import quotes.reflect.*

    object processor extends
      Component.withQuotes(quotes),
      Commons,
      ErrorReporter,
      Annotations,
      Placements,
      Peers,
      Access,
      PlacedTransformations,
      PlacedStatements,
      PlacedExpressions,
      Synthesis,
      Splitting

    tree match
      case tree: ClassDef =>
        val phases = List(
          processor.normalizePlacedStatements,
          processor.eraseMultitierConstructs,
          processor.split)

        val processed = phases.foldLeft(tree): (tree, process) =>
          if processor.canceled then tree else process(tree)

        processor.reportErrors()

        APIExtraction.extractAPI(processed)

        println(processed.show)

        List(processed)

      case _ =>
        report.errorAndAbort("multitier annotation only applicable to classes, traits or objects")
  end annotation
end Multitier
