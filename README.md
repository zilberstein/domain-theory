# Domain Theory in Lean

This library defined basic concepts from domain theory, following [Abramsky and Jung 1995](https://achimjungbham.github.io/pub/papers/handy1.pdf).
Domain Theory is useful for defining denotational semantics of programming languages, particularly probabilistic languages.

Although mathlib aleady defines a `CompletePartialOrder` class, that class is painful to use because it extends `SupSet` and `OrderBot`.
`SupSet` is problematic because it requires one to define a supremum of any arbitrary set, whereas in many cases the supremum only exists for a directed set.
`OrderBot` is problematic because some DCPOs do not have a least element, if they do have a least element, then they are called *pointed* DCPOs.
Moreover, directed sets must be nonempty, which is not imposed in mathlib's `CompletePartialOrder` class.
By contrast, this library more closely follows the established theory.
The implementation is closer to mathlib's `OmegaCompletePartialOrder` class, which only requires giving a supremum of an omega chain rather than an arbitrary set.