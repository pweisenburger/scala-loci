package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait RemoteAccessorGeneration:
  this: Component & Commons & Peers & RemoteAccessorSynthesis =>
  import quotes.reflect.*

  def materializeDummySignatures(module: ClassDef): ClassDef =
    val symbol = module.symbol

    val erased = Ref(symbols.erased).appliedToType(TypeRepr.of[Nothing])

    def dummy(symbol: Symbol) =
      if symbol.isMethod then DefDef(symbol, _ => Some(erased)) else ValDef(symbol, Some(erased))

    val (identifier, signature) = synthesizeModuleSignature(symbol)

    val peerDefinitions =
      PeerInfo.ofModule(symbol) flatMap: peerInfo =>
        val peer = peerInfo.peerType.typeSymbol
        if peer != defn.AnyClass then
          val (signature, ties) = synthesizePeerSignature(symbol, peer)
          List(dummy(signature), dummy(ties))
        else
          List.empty

    val definitions = dummy(identifier) :: dummy(signature) :: peerDefinitions

    definitions foreach: definition =>
      SymbolMutator.getOrErrorAndAbort.setFlag(definition.symbol, Flags.Artifact)

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, definitions ++ module.body)
  end materializeDummySignatures

  def materializeAccessors(module: ClassDef): ClassDef =
    val accessors = synthesizeAccessors(module.symbol)

    val (_, identifierDefinition) = accessors.identifier
    val (_, signatureDefinition) = accessors.signature

    val peersDefinitions = accessors.peers.values flatMap: (_, signatureDefinition, _, tiesDefinition) =>
      signatureDefinition.toList ++ tiesDefinition.toList
    val marshallingDefinitions = accessors.overridden.iterator ++ accessors.marshalling.iterator flatMap: (_, definition) =>
      definition.toList
    val placedDefinitions = accessors.placed.values flatMap: (_, definition) =>
      definition.toList

    val definitions =
      identifierDefinition.toList ++
      signatureDefinition.toList ++
      peersDefinitions.toList ++
      marshallingDefinitions.toList ++
      placedDefinitions.toList

    val signatures =
      (identifierDefinition.iterator ++
       signatureDefinition.iterator ++
       peersDefinitions.iterator map { _.symbol }).toSet

    signatures foreach: symbol =>
      if symbol.flags is Flags.Artifact then
        SymbolMutator.getOrErrorAndAbort.resetFlag(symbol, Flags.Artifact)

    val body = module.body filterNot:
      case stat: Definition => signatures contains stat.symbol
      case _ => false

    ClassDef.copy(module)(module.name, module.constructor, module.parents, module.self, definitions ++ body)
  end materializeAccessors
end RemoteAccessorGeneration
