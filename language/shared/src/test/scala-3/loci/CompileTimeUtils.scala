package loci

import embedding.impl.*
import scala.quoted.*

extension (inline compileTimeUtils: CompileTimeUtils.type)
  transparent inline def exposeSynthesizedMultitierValues(inline multitierModule: Any): Unit =
    ${ exposeSynthesizedMultitierValuesImpl('multitierModule) }

object exposeSynthesizedMultitierValuesImpl:
  def apply(multitierModule: Expr[Any])(using Quotes) =
    import quotes.reflect.*

    val module = multitierModule.asTerm.underlyingArgument.symbol
    val symbolMutator = SymbolMutator.getOrErrorAndAbort
    val engine = ResolverEngine(quotes)

    import engine.*

    symbolMutator.resetFlag(moduleIdentifier(module), Flags.Invisible)
    symbolMutator.resetFlag(moduleSignature(module), Flags.Invisible)

    PeerInfo.ofModule(module) foreach: peerInfo =>
      val peer = peerInfo.peerType.typeSymbol
      symbolMutator.resetFlag(peerTies(module, peer), Flags.Invisible)
      symbolMutator.resetFlag(peerSignature(module, peer), Flags.Invisible)
      symbolMutator.resetFlag(placedValues(module, peer), Flags.Invisible)

    marshallingAccessor(module) foreach: accessor =>
      symbolMutator.resetFlag(accessor, Flags.Invisible)
      symbolMutator.resetFlag(accessor, Flags.Protected)

    placedAccessor(module) foreach: accessor =>
      symbolMutator.resetFlag(accessor, Flags.Invisible)
      symbolMutator.resetFlag(accessor, Flags.Protected)

    '{ () }
