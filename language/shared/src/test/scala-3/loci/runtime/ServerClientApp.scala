package loci
package runtime

import loci.language.*
import loci.serializer.Serializables.*

@multitier object ServerClientApp:
  @peer type Server <: { type Tie <: Multiple[Client] }
  @peer type Client <: { type Tie <: Single[Server] }

  val id = on[Client] { 0 }

  def square(a: Int) = on[Server] { a * a }
