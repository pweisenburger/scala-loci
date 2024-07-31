package loci
package embedding

def erased[T]: T = erased()
def erased[T](ev: Any*): T =
  throw new NotImplementedError("Erased language constructs should never be used")
