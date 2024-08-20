package loci
package language
package transmitter

infix type from[T, R] = embedding.PlacedValue.Resolution[R, T]

type Gateway[R] = embedding.Gateway[R]

type Single = embedding.Tie.Single
type Optional = embedding.Tie.Optional
type Multiple = embedding.Tie.Multiple
