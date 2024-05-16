package loci
package embedding
package impl
package components

import utility.reflectionExtensions.*

import scala.annotation.experimental

@experimental
trait AccessPath:
  this: Component & Commons & PlacedValueSynthesis =>
  import quotes.reflect.*

  private def multitierOuterAccess(from: Symbol, to: Symbol, peer: Symbol) =
    def multitierOuterAccess(symbol: Symbol, path: Term): Option[Term] =
      if symbol == to then
        Some(path)
      else
        val outerAccessor = synthesizedPlacedValues(symbol, defn.AnyClass).symbol.fieldMembers find: member =>
          member.isParamAccessor && member.info.typeSymbol == synthesizedPlacedValues(symbol.owner, defn.AnyClass).symbol
        outerAccessor flatMap { outerAccessor => multitierOuterAccess(symbol.owner, path.select(outerAccessor)) }

    multitierOuterAccess(from, This(synthesizedPlacedValues(from, peer).symbol))
  end multitierOuterAccess

  private def multitierAccessSymbol(symbol: Symbol, from: Symbol, peer: Symbol): Option[Term] =
    if isMultitierModule(symbol) && (from hasAncestor symbol) then
      multitierOuterAccess(from, symbol, peer)
    else if isMultitierNestedPath(symbol) then
      synthesizedDefinitions(symbol) flatMap: definition =>
        multitierAccessPath(This(symbol.owner), from, peer) map { _.select(definition.binding) }
    else
      None

  def multitierAccessPath(path: Term, from: Symbol, peer: Symbol): Option[Term] =
    termAsSelection(path, from) getOrElse path match
      case Ident(_) =>
        multitierAccessSymbol(path.symbol.moduleClass, from, peer)
      case This(_) =>
        multitierAccessSymbol(path.symbol, from, peer)
      case Super(qualifier @ This(_), identifier) if qualifier.symbol == from =>
        val thisReference = This(synthesizedPlacedValues(from, peer).symbol)
        identifier.fold(Some(Super(thisReference, None))): identifier =>
          qualifier.symbol.typeRef.baseClasses filter { _.name == identifier } match
            case List(parent) if isMultitierModule(parent) =>
              Some(Super(thisReference, Some(synthesizedPlacedValues(parent, defn.AnyClass).symbol.name)))
            case _ =>
              None
      case Select(qualifier, _) =>
        if isMultitierModule(path.symbol) &&
           !isMultitierNestedPath(qualifier.symbol) &&
           isStablePath(qualifier) &&
           path.symbol.moduleClass.exists &&
           (from hasAncestor path.symbol.moduleClass) then
          multitierOuterAccess(from, path.symbol.moduleClass, peer)
        else if isMultitierNestedPath(qualifier.symbol) then
          synthesizedDefinitions(path.symbol) flatMap: definition =>
            multitierAccessPath(qualifier, from, peer) map { _.select(definition.binding) }
        else
          None
      case _ =>
        None
  end multitierAccessPath
end AccessPath
