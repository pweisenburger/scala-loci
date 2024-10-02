package loci
package embedding
package impl

import components.*
import utility.reflectionExtensions.*

import scala.annotation.experimental
import scala.quoted.*

@experimental
object Multitier:
  def annotation(using Quotes)(tree: quotes.reflect.Definition, companion: Option[quotes.reflect.Definition]): List[quotes.reflect.Definition] =
    import quotes.reflect.*

    object processor extends
      Component.withQuotes(quotes),
      Commons,
      ErrorReporter,
      AccessNotation,
      Annotations,
      SymbolTrees,
      Placements,
      NonPlacements,
      Peers,
      AccessPath,
      PlacedTransformations,
      PlacedStatements,
      PlacedBlocks,
      PlacedExpressions,
      PlacedValueSynthesis,
      RemoteAccessorSynthesis,
      PlacedValueSplitting,
      RemoteAccessorGeneration,
      Invocation,
      Dispatch

    import processor.*

    val preprocessingPhases = List(
      normalizePlacedStatements,
      liftRemoteBlocks,
      eraseMultitierConstructs)

    val processingPhases = List(
      split,
      materializeAccessors,
      rewireInvocations,
      generateDispatching)

    class Preprocessor extends SafeTreeMap(quotes):
      def trySwapMultitierAnnotation(symbol: Symbol) =
        SymbolMutator.get foreach: symbolMutator =>
          val instantiation = New(TypeIdent(symbols.`embedding.multitier`))
          val annotation =
            multitierModuleArgument(symbol) match
              case Some(arg) => instantiation.select(symbols.`embedding.multitier`.declarations.last).appliedTo(arg)
              case _ => instantiation.select(symbols.`embedding.multitier`.declarations.head).appliedToNone
          symbolMutator.removeAnnotation(symbol, symbols.`language.multitier`)
          symbolMutator.updateAnnotationWithTree(symbol, annotation)

      override def transformTerm(term: Term)(owner: Symbol) =
        if canceled then term else super.transformTerm(term)(owner)

      override def transformStatement(stat: Statement)(owner: Symbol) =
        super.transformStatement(stat)(owner) match
          case stat: ValDef if stat.symbol.hasAnnotation(symbols.`language.multitier`) =>
            trySwapMultitierAnnotation(stat.symbol)
            symbolOriginalTree(stat.symbol) = stat
            stat

          case stat: ClassDef if isMultitierModule(stat.symbol) =>
            trySwapMultitierAnnotation(stat.symbol)
            symbolOriginalTree(stat.symbol) = stat

            preprocessingPhases.foldLeft(stat): (stat, process) =>
              if !canceled then
                val processed = process(stat)

                symbolTree(processed.symbol) = processed
                processed.body foreach:
                  case stat: Definition => symbolTree(stat.symbol) = stat
                  case _ =>

                processed
              else
                stat

          case stat: Definition =>
            symbolOriginalTree(stat.symbol) = stat
            stat

          case stat =>
            stat
    end Preprocessor

    class Processor(skip: Boolean) extends SafeTreeMap(quotes):
      override def transformStatement(stat: Statement)(owner: Symbol) =
        super.transformStatement(stat)(owner) match
          case stat: ClassDef if isMultitierModule(stat.symbol) =>
            val processed =
              if !skip then
                processingPhases.foldLeft(stat): (stat, process) =>
                  val processed = process(stat)

                  symbolTree(processed.symbol) = processed
                  processed.body foreach :
                    case stat: Definition => symbolTree(stat.symbol) = stat
                    case _ =>

                  processed
              else
                stat

            APIExtraction.extractAPI(processed)
            processed

          case stat =>
            stat
    end Processor

    tree match
      case _: ClassDef | _: ValDef if tree.symbol.owner hasAncestor isMultitierModule =>
        List(tree) ++ companion

      case _: ClassDef =>
        object preprocessor extends Preprocessor
        val preprocessed = preprocessor.transformSubTrees(List(tree))(tree.symbol.owner).head

        object processor extends Processor(canceled)
        val processed = processor.transformSubTrees(List(preprocessed))(tree.symbol.owner).head

        reportErrors(abortOnErrors = true)
        List(processed) ++ companion

      case _ =>
        report.error(
          s"${prettyAnnotation("@multitier")} annotation is only applicable to classes, traits or objects " +
           "and to values nested inside multitier classes, traits or objects.")
        List(tree) ++ companion
  end annotation
end Multitier
