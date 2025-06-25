package loci
package embedding

import loci.language.{on as _, *}

import scala.annotation.experimental
import scala.quoted.*

object On:
  def apply[P: Type](using Quotes) =
    import quotes.reflect.*
    '{ erased: On[P] & Run[P, from] } match
      case expr: Expr[On.Fallback[P] & Run[P, from]] @unchecked => expr

  trait Fallback[P]:
    @experimental
    transparent inline def apply[T, U](inline v: Placement.Context[P] ?=> T)(using PlacedClean[T, T, U]): U on P =
      ${ impl.inferrableCanonicalPlacementTypeContextClosure[U on P]('{ v(using erased[Placement.Context[P]]) }) }
    @experimental
    transparent inline infix def local[T, U](inline v: Placement.Context[P] ?=> T)(using PlacedClean[T, T, U]): Local[U] on P =
      ${ impl.inferrableCanonicalPlacementTypeContextClosure[Local[U] on P]('{ v(using erased[Placement.Context[P]]) }) }
    @experimental
    transparent inline infix def sbj[R, T, U](inline v: Placement.Context[P] ?=> Remote[R] => T)(using PlacedClean[T, T, U]): U per R on P =
      ${ impl.inferrableCanonicalPlacementTypeContextClosure[U per R on P]('{ v(using erased[Placement.Context[P]]) }) }

  trait Placed:
    @experimental
    transparent inline def apply[T, P](using Placed.Context)(using Placement.Context.ResolutionWithFallback[P])(inline v: Placement.Context[P] ?=> T): T on P =
      ${ impl.inferrableCanonicalPlacementTypeContextClosure[T on P]('{ v(using erased[Placement.Context[P]](summon[Placed.Context])) }) }

  object Placed extends Placed:
    sealed trait Context
    given Context()
end On

trait On[P]:
  @experimental
  transparent inline def apply[T](inline v: Placement.Context[P] ?=> T): T on P =
    ${ impl.inferrableCanonicalPlacementTypeContextClosure[T on P]('{ v(using erased[Placement.Context[P]]) }) }
  @experimental
  transparent inline infix def local[T](inline v: Placement.Context[P] ?=> T): Local[T] on P =
    ${ impl.inferrableCanonicalPlacementTypeContextClosure[Local[T] on P]('{ v(using erased[Placement.Context[P]]) }) }
  @experimental
  transparent inline infix def sbj[R, T](inline v: Placement.Context[P] ?=> Remote[R] => T): T per R on P =
    ${ impl.inferrableCanonicalPlacementTypeContextClosure[T per R on P]('{ v(using erased[Placement.Context[P]]) }) }

trait Select[Command[_, _[_, _]]]:
  def apply(r: Select.Remote[?, ?]): Command[r.Peer, r.placed] = erased
  def apply[P](r0: Remote[P], r1: Remote[P], rn: Remote[P]*): Command[P, fromMultiple] = erased

//  def apply(r: Remote[?] on ?)(using remote: Select.RemoteType[r.type]): Command[remote.Type, fromSingle] = erased
//  def apply(r: Remote[?])(using remote: Select.RemoteType[r.type]): Command[remote.Type, fromSingle] = erased
//  def apply[P](r0: Remote[P], r1: Remote[P], rn: Remote[P]*): Command[P, fromMultiple] = erased
//  def apply(r: Seq[Remote[?]])(using remote: Select.RemoteSeqType[r.type]): Command[remote.Type, fromMultiple] = erased

//  def apply[P, Q, _on_[T, P] <: T on P](r: Remote[P] _on_ Q): Command[P, fromSingle] = erased
//  def apply[P, Disambiguation](r: Remote[P]): Command[P, fromSingle] = erased
//  def apply[P, Disambiguation](r0: Remote[P], r1: Remote[P], rn: Remote[P]*): Command[P, fromMultiple] = erased
//  def apply[P, Disambiguation](r: Seq[Remote[P]]): Command[P, fromMultiple] = erased

object Select:
  object Run extends Select[Run]
  object Call extends Select[Call]

  final class Remote[P, p[_, _]](remotes: Seq[language.Remote[P]]):
    type Peer = P
    type placed = [T, P] =>> p[T, P]

  inline given liftRemote[P]: Conversion[language.Remote[P], Select.Remote[P, [T, P] =>> T fromSingle P]] with
    transparent inline def apply(remote: language.Remote[P]) = Select.Remote(Seq(remote))
  inline given liftRemotePlaced[P]: Conversion[language.Remote[P] on ?, Select.Remote[P, [T, P] =>> T fromSingle P]] with
    transparent inline def apply(remote: language.Remote[P] on ?) = Select.Remote(Seq(remote))
  inline given liftRemoteSeq[P]: Conversion[Seq[language.Remote[P]], Select.Remote[P, [T, P] =>> T fromMultiple P]] with
    transparent inline def apply(remotes: Seq[language.Remote[P]]) = Select.Remote(remotes)

//  sealed trait RemoteType[-T] { type Type }
//  sealed trait RemoteSeqType[-T] { type Type }
//  given [T, U](using T <:< Remote[U]): (RemoteType[T] { type Type = U }) = erased
//  given [T, U](using T <:< Seq[Remote[U]]): (RemoteSeqType[T] { type Type = U }) = erased

trait Run[P, placed[_, _]]

object Run:
  extension [P, R, placed[_, _]](run: Run[P, placed])(using Placement.Context.Resolution[R]) def run: Capture[P, R, placed] & Block[P, R, placed] = erased

trait Capture[P, R, placed[_, _]]:
  def capture(v: Any*): Block[P, R, placed] = erased

trait Block[P, R, placed[_, _]]:
  def apply[T, U](v: Placement.Context[P] ?=> T)(using PlacedClean[T, T, U]): U placed P = erased
  infix def sbj[T, U](v: Placement.Context[P] ?=> Remote[R] => T)(using PlacedClean[T, T, U]): U per R placed P = erased

trait Narrow:
  infix def value[P, T, _on_[T, P] <: T on P](v: T _on_ P): T placed P = erased

trait Call[Q, placed[_, _]]:
  infix def call[P, R, T, _on_[T, P] <: T on P](v: T _on_ R)(using PeerType[Q, R, P]): T placed P = erased
