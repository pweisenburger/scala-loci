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

    object engine extends
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
      Checking,
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

    import engine.*

    val preprocessingPhases = List(
      checkMultitierDefinitions,
      normalizePlacedStatements,
      checkDeferredDefinitions,
      liftRemoteBlocks,
      eraseMultitierConstructs)

    val processingPhases = List(
      split,
      materializeAccessors,
      rewireInvocations,
      generateDispatching)

    object preprocessor extends SafeTreeMap(quotes):
      def trySwapMultitierAnnotation(symbol: Symbol) =
        SymbolMutator.get foreach: symbolMutator =>
          val instantiation = New(TypeIdent(symbols.`embedding.multitier`))
          val annotation =
            multitierModuleArgument(symbol) match
              case Some(arg) => instantiation.select(symbols.`embedding.multitier`.declarations.last).appliedTo(arg)
              case _ => instantiation.select(symbols.`embedding.multitier`.declarations.head).appliedToNone
          symbolMutator.removeAnnotation(symbol, symbols.`language.multitier`)
          symbolMutator.updateAnnotationWithTree(symbol, annotation)

      override def transformStatement(stat: Statement)(owner: Symbol) = stat match
        case stat: ClassDef if isMultitierModule(stat.symbol) =>
          trySwapMultitierAnnotation(stat.symbol)
          symbolOriginalTree(stat.symbol) = stat

          val preprocessed =
            preprocessingPhases.foldLeft(stat): (stat, process) =>
              process(stat)

          symbolPreprocessedTree(preprocessed.symbol) = preprocessed
          preprocessed.body foreach:
            case stat: Definition => symbolPreprocessedTree(stat.symbol) = stat
            case _ =>

          super.transformStatement(preprocessed)(owner)

        case stat: Definition =>
          if stat.symbol.hasAnnotation(symbols.`language.multitier`) then
            trySwapMultitierAnnotation(stat.symbol)
          symbolOriginalTree(stat.symbol) = stat
          super.transformStatement(stat)(owner)

        case stat =>
          super.transformStatement(stat)(owner)
    end preprocessor

    object processor extends SafeTreeMap(quotes):
      override def transformStatement(stat: Statement)(owner: Symbol) =
        super.transformStatement(stat)(owner) match
          case stat: ClassDef if isMultitierModule(stat.symbol) =>
            val processed =
              processingPhases.foldLeft(stat): (stat, process) =>
                process(stat)

            APIExtraction.extractAPI(processed)
            processed

          case stat =>
            stat
    end processor

    tree match
      case _: ClassDef | _: ValDef if tree.symbol.owner hasAncestor isMultitierModule =>
        List(tree) ++ companion

      case tree: ClassDef =>
        checkMultitierAnnotations(tree)

        val preprocessed =
          preprocessor.transformSubTrees(List(tree))(tree.symbol.owner).head

        val processed =
          if !canceled then
            processor.transformSubTrees(List(preprocessed))(tree.symbol.owner).head
          else
            preprocessed

        reportErrors(abortOnErrors = true)

        List(processed) ++ companion

      case _ =>
        report.error(
          s"${prettyAnnotation("@multitier")} annotation is only applicable to classes, traits or objects " +
           "and to values nested inside multitier classes, traits or objects.")
        List(tree) ++ companion
  end annotation
end Multitier
