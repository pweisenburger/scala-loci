package loci
package embedding

import loci.language.{multitier as _, *}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import scala.annotation.experimental
import scala.concurrent.Future

class TypeLevelEncodingSpec extends AnyFlatSpec with Matchers with NoLogging:
  behavior of "Type Level Encoding"

  it should "typecheck remote access" in:
    CompileTimeUtils.assertNoFailedAssertion:
      @experimental
      @multitier
      trait Module:
        @peer type Component
        @peer type Server <: Component { type Tie <: Multiple[Client] & Optional[MobileClient] }
        @peer type Client <: Component { type Tie <: Single[Server] & Single[SpecialServer] }
        @peer type MobileClient <: Client { type Tie <: Single[Server] & Single[SpecialServer] }
        @peer type SpecialServer <: Server { type Tie <: Multiple[Client] & Optional[MobileClient] }


        val server: Remote[Server] = ???
        val client: Remote[Client] = ???


        val a0: Int on Server = 42
        val a1 = on[Server] { a0 to server }
        val a2 = on[Server] sbj { (v: Remote[Client]) => a0 to server }

        CompileTimeUtils.assertExactType[Int on Server, a0.type]
        CompileTimeUtils.assertExactType[Int per Client on Server, a2.type]


        val b0: Local[Int] on Client = 42
        val b1 = on[Client] local { b0 to server }
        val b2 = on[Client] sbj { (v: Remote[Server]) => b0 to server }

        CompileTimeUtils.assertExactType[Local[Int] on Client, b1.type]
        CompileTimeUtils.assertExactType[Int per Server on Client, b2.type]


        val c0: Int on Client = b0
        val c1 = on[Client] { b0 }
        val c2 = on[Client] sbj { (v: Remote[Server]) => b0 }

        CompileTimeUtils.assertExactType[Int on Client, c1.type]
        CompileTimeUtils.assertExactType[Int per Server on Client, c2.type]


        val d0: Int per Server on Client = (v: Remote[Server]) => 42
        val d1 = on[Client] { c0 to server }
        val d2 = on[Client] sbj { (v: Remote[Server]) => c0 to server }

        CompileTimeUtils.assertExactType[Int on Client, d1.type]
        CompileTimeUtils.assertExactType[Int per Server on Client, d2.type]


        val e0: Unit per Server on Client = (v: Remote[Server]) => d0
        val e1 = on[Client] { d0 }
        val e2 = on[Client] sbj { (v: Remote[Server]) => d0 }

        CompileTimeUtils.assertExactType[Unit on Client, e1.type]
        CompileTimeUtils.assertExactType[Unit per Server on Client, e2.type]


        val f0: Option[Int] on Client = Option(c0)
        val f1 = on[Client] { Option(c0) }
        val f2 = on[Client] sbj { (v: Remote[Server]) => Option(c0) }

        CompileTimeUtils.assertExactType[Option[Int] on Client, f1.type]
        CompileTimeUtils.assertExactType[Option[Int] per Server on Client, f2.type]


        val g0: Nothing on Client = ???
        val g1 = on[Client] { ??? }
        val g2 = on[Client] { g0 }
        val g3 = on[Client] sbj { (v: Remote[Server]) => ??? }
        val g4 = on[Client] sbj { (v: Remote[Server]) => g0 }

        CompileTimeUtils.assertExactType[Nothing of Client on Client, g1.type]
        CompileTimeUtils.assertExactType[Nothing of Client on Client, g2.type]
        CompileTimeUtils.assertExactType[Nothing per Server on Client, g3.type]
        CompileTimeUtils.assertExactType[Nothing per Server on Client, g4.type]


        val h0: Local[Nothing] on Client = ???
        val h1 = on[Client] local { ??? }
        val h2 = on[Client] local { h0 }
        val h3 = on[Client] sbj { (v: Remote[Server]) => ??? }
        val h4 = on[Client] sbj { (v: Remote[Server]) => h0 }

        CompileTimeUtils.assertExactType[Local[Nothing] of Client on Client, h1.type]
        CompileTimeUtils.assertExactType[Local[Nothing] of Client on Client, h2.type]
        CompileTimeUtils.assertExactType[Nothing per Server on Client, h3.type]
        CompileTimeUtils.assertExactType[Nothing per Server on Client, h4.type]


        val i0: Any on Client = 42: Any
        val i1 = on[Client] { 42: Any }
        val i2 = on[Client] { i0 }
        val i3 = on[Client] sbj { (v: Remote[Server]) => 42: Any }
        val i4 = on[Client] sbj { (v: Remote[Server]) => i0 }

        CompileTimeUtils.assertExactType[Any on Client, i1.type]
        CompileTimeUtils.assertExactType[Any on Client, i2.type]
        CompileTimeUtils.assertExactType[Any per Server on Client, i3.type]
        CompileTimeUtils.assertExactType[Any per Server on Client, i4.type]


        val j0: Local[Any] on Client = 42: Any
        val j1 = on[Client] local { 42: Any }
        val j2 = on[Client] local { j0 }
        val j3 = on[Client] sbj { (v: Remote[Server]) => 42: Any }
        val j4 = on[Client] sbj { (v: Remote[Server]) => j0 }

        CompileTimeUtils.assertExactType[Local[Any] on Client, j1.type]
        CompileTimeUtils.assertExactType[Local[Any] on Client, j2.type]
        CompileTimeUtils.assertExactType[Any per Server on Client, j3.type]
        CompileTimeUtils.assertExactType[Any per Server on Client, j4.type]


        val k0 = on[Server] { remote call c0 }
        val k1 = on[Server] { remote call d0 }
        val k2 = on[Server] { remote[MobileClient] call c0 }
        val k3: on[Unit, Server] = on[Server] { remote(client) call c0 }
        val k4 = on[Server] { remote(client, client) call c0 }

        CompileTimeUtils.assertExactType[Unit on Server, k0.type]
        CompileTimeUtils.assertExactType[Unit on Server, k1.type]
        CompileTimeUtils.assertExactType[Unit on Server, k2.type]
        CompileTimeUtils.assertExactType[Unit on Server, k3.type]
        CompileTimeUtils.assertExactType[Unit on Server, k4.type]


        val l0 = on[Server] { (remote call c0).asLocalFromAll }
        val l1 = on[Server] { (remote call d0).asLocalFromAll }
        val l2 = on[Server] { (remote[MobileClient] call c0).asLocal }
        val l3 = on[Server] { (remote(client) call c0).asLocal }
        val l4 = on[Server] { (remote(client, client) call c0).asLocalFromAll }

        CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])] on Server, l0.type]
        CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])] on Server, l1.type]
        CompileTimeUtils.assertExactType[Option[Future[Int]] on Server, l2.type]
        CompileTimeUtils.assertExactType[Future[Int] on Server, l3.type]
        CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])] on Server, l4.type]


        on[Server]:
          val a = c0.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])], a.type]

          val b = d0.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])], b.type]

          val c = d0.from[MobileClient].asLocal
          CompileTimeUtils.assertExactType[Option[Future[Int]], c.type]

          val d = (d0 from client).asLocal
          CompileTimeUtils.assertExactType[Future[Int], d.type]

          val e = (d0 from (client, client)).asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])], e.type]

          // `b0.asLocalFromAll` should not work since `b0` is local
          // this, however, is only checked during macro expansion
          val f = b0.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Int])], f.type]

          val g = g2.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Nothing])], g.type]

          val h = g4.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Nothing])], h.type]

          val i = g4.from[MobileClient].asLocal
          CompileTimeUtils.assertExactType[Option[Future[Nothing]], i.type]

          val j = (g4 from client).asLocal
          CompileTimeUtils.assertExactType[Future[Nothing], j.type]

          val k = (g4 from (client, client)).asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Nothing])], k.type]

          // `h2.asLocalFromAll` should not work since `h2` is local
          // this, however, is only checked during macro expansion
          val l = h2.asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Client], Future[Nothing])], l.type]


        on[Client]:
          val a = a0.asLocal
          CompileTimeUtils.assertExactType[Future[Int], a.type]

          val b = a0.from[SpecialServer].asLocal
          CompileTimeUtils.assertExactType[Future[Int], b.type]

          val c = (a0 from server).asLocal
          CompileTimeUtils.assertExactType[Future[Int], c.type]

          val d = (a0 from (server, server)).asLocalFromAll
          CompileTimeUtils.assertExactType[Seq[(Remote[Server], Future[Int])], d.type]


        on[Client]:
          val value = 42

          // access from the client to the client should not work for the specified architecture
          // this, however, is only checked during macro expansion
          val a = on(client).run { 42 }
          CompileTimeUtils.assertType[Int fromSingle Client, a.type]

          val b = on(server, server).run { 42 }
          CompileTimeUtils.assertType[Int fromMultiple Server, b.type]

          val c = on[Server].run { 42 }
          CompileTimeUtils.assertType[Int from Server, c.type]

          val d = on[Server].run.capture(value) { 42 }
          CompileTimeUtils.assertType[Int from Server, d.type]

          // remote blocks with a subjective value for a peer different from the current peer should not work
          // this, however, is only checked during macro expansion
          val e = on(server).run sbj { (v: Remote[Client]) => 42 }
          CompileTimeUtils.assertType[Int per Client fromSingle Server, e.type]

          val f = on(server, server).run sbj { (v: Remote[Client]) => 42 }
          CompileTimeUtils.assertType[Int per Client fromMultiple Server, f.type]

          val g = on[Server].run sbj { (v: Remote[Client]) => 42 }
          CompileTimeUtils.assertType[Int per Client from Server, g.type]

          val h = on[Server].run.capture(value) sbj { (v: Remote[Client]) => 42 }
          CompileTimeUtils.assertType[Int per Client from Server, h.type]
end TypeLevelEncodingSpec
