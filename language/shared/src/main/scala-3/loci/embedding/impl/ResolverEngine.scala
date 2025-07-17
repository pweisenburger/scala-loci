package loci
package embedding
package impl

import components.*
import utility.reflectionExtensions.*
import scala.annotation.{experimental, targetName}
import scala.quoted.*

trait ResolverEngine[Q <: Quotes & Singleton](val quotes: Q):
  import quotes.reflect.*

  private given quotes.type = quotes

  def prettyShowType(tpe: TypeRepr): String
  def prettyShowTerm(term: Term): String

  def isMultitierModule(symbol: Symbol): Boolean
  def moduleIdentifier(module: Symbol): Symbol
  def moduleSignature(module: Symbol): Symbol
  def peerTies(module: Symbol, peer: Symbol): Symbol
  def peerSignature(module: Symbol, peer: Symbol): Symbol
  def marshallingAccessor(module: Symbol): List[Symbol]
  def placedAccessor(module: Symbol): List[Symbol]
  def placedValues(module: Symbol, peer: Symbol): Symbol

  enum Multiplicity:
    case Single, Optional, Multiple

  case class PeerInfo(peerType: TypeRef, parents: List[TypeRef], ties: List[(TypeRef, Multiplicity)])

  object PeerInfo:
    def apply(tpe: TypeRepr) = peerInfo(tpe)
    def check(tpe: TypeRepr, pos: Position = Position.ofMacroExpansion) = peerInfoCheck(tpe, pos)
    def check(tree: TypeDef) = peerInfoCheck(tree)
    def check(tree: TypeDef, shallow: Boolean) = peerInfoCheck(tree, shallow)
    @targetName("ofModuleSymbol") def ofModule(symbol: Symbol) = peerInfoOfModule(symbol)
    @targetName("ofModuleType") def ofModule(tpe: TypeRepr) = peerInfoOfModule(tpe)

  protected def peerInfo(tpe: TypeRepr): Option[PeerInfo]
  protected def peerInfoCheck(tpe: TypeRepr, pos: Position): Either[(String, Position), PeerInfo]
  protected def peerInfoCheck(tree: TypeDef): Either[(String, Position), PeerInfo]
  protected def peerInfoCheck(tree: TypeDef, shallow: Boolean): Either[(String, Position), PeerInfo]
  @targetName("peerInfoOfModuleSymbol") protected def peerInfoOfModule(symbol: Symbol): List[PeerInfo]
  @targetName("peerInfoOfModuleType") protected def peerInfoOfModule(tpe: TypeRepr): List[PeerInfo]
end ResolverEngine

object ResolverEngine:
  def apply(quotes: Quotes) =
    classOf[ResolverEngine.type].getDeclaredMethod("construct", classOf[Quotes]).invoke(this, quotes) match
      case engine: ResolverEngine[quotes.type] @unchecked => engine

  @experimental
  private def construct(using Quotes) =
    import quotes.reflect.*

    object engine extends
      Component.withQuotes(quotes),
      Commons, ErrorReporter, Annotations, SymbolTrees, Placements, NonPlacements, Peers, PlacedTransformations,
      PlacedValueSynthesis, RemoteAccessorSynthesis

    new ResolverEngine(quotes):
      def prettyShowType(tpe: TypeRepr) = engine.prettyType(engine.prettyShow(tpe))
      def prettyShowTerm(term: Term) = engine.prettyType(term.safeShow)

      def isMultitierModule(symbol: Symbol) = engine.isMultitierModule(symbol)
      def moduleIdentifier(module: Symbol) = engine.synthesizeAccessors(module).identifier.head
      def moduleSignature(module: Symbol) = engine.synthesizeAccessors(module).signature.head
      def peerTies(module: Symbol, peer: Symbol) = engine.synthesizeAccessors(module).peers.get(peer).fold(Symbol.noSymbol) { (_, _, ties, _) => ties }
      def peerSignature(module: Symbol, peer: Symbol) = engine.synthesizeAccessors(module).peers.get(peer).fold(Symbol.noSymbol) { (signature, _, _, _) => signature }
      def marshallingAccessor(module: Symbol) = (engine.synthesizeAccessors(module).marshalling.iterator map { (marshalling, _) => marshalling }).toList
      def placedAccessor(module: Symbol) = (engine.synthesizeAccessors(module).placed.valuesIterator map { (placed, _) => placed }).toList
      def placedValues(module: Symbol, peer: Symbol) = engine.synthesizedPlacedValues(module, peer).symbol

      private def convertPeerInfo(peerInfo: engine.PeerInfo) =
        PeerInfo(peerInfo.peerType, peerInfo.parents, peerInfo.ties map { (tpe, multiplicity) => tpe -> Multiplicity.fromOrdinal(multiplicity.ordinal) })

      def peerInfo(tpe: TypeRepr) = engine.PeerInfo(tpe) map convertPeerInfo
      def peerInfoCheck(tpe: TypeRepr, pos: Position) = engine.PeerInfo.check(tpe, pos) map convertPeerInfo
      def peerInfoCheck(tree: TypeDef) = engine.PeerInfo.check(tree) map convertPeerInfo
      def peerInfoCheck(tree: TypeDef, shallow: Boolean) = engine.PeerInfo.check(tree, shallow) map convertPeerInfo
      @targetName("peerInfoOfModuleSymbol") def peerInfoOfModule(symbol: Symbol) = engine.PeerInfo.ofModule(symbol) map convertPeerInfo
      @targetName("peerInfoOfModuleType") def peerInfoOfModule(tpe: TypeRepr) = engine.PeerInfo.ofModule(tpe) map convertPeerInfo
  end construct
end ResolverEngine
