import Mathlib
import Submission.Cohomology.ConormalH1Cotangent
import Submission.Cohomology.ConormalToOmega

/-!
# The cotangent inequality: `embedding dimension ≤ rank Ω`

For a local ring `R` with separable (formally-smooth) residue field over `k` and finite `Ω[R⁄k]`,
the conormal module of the residue presentation injects into `κ ⊗_R Ω[R⁄k]` (brick (b5)-core),
hence

`finrank_κ (𝔪/𝔪²) ≤ finrank_R Ω[R⁄k]`   (= rel dim for `IsStandardSmooth`).

This is leaf-(b) sub-brick **(b5)-finish (inequality half)** of the `smooth ⇒ regular local` chain
(route doc §"leaf (b) scoped"). It turns the (b5)-core *injection* into a *finrank bound* via
`LinearMap.finrank_le_finrank_of_injective` (the codomain `κ⊗Ω` is finite over `κ` since `Ω` is
finite over `R`) and `Module.finrank_baseChange` (`finrank_κ(κ⊗Ω) = rank_R Ω`).

Here we prove the **unconditional inequality** `finrank_κ((trivExt 𝔪).Cotangent) ≤ rank_R Ω[R⁄k]`.
Two glue steps remain to reach `IsRegularLocalRing` via
`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`, both recorded in the route doc as the (b5)
residual: (i) the transport `(trivExt 𝔪).Cotangent ≅ IsLocalRing.CotangentSpace R` (a `LinearEquiv`
from `(trivExt 𝔪).ker = 𝔪`, crossing the `ResidueField R` ↔ `R⧸𝔪` scalar duality) feeding
`spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`; and (ii) the local-ring dimension
`ringKrullDim R = rank_R Ω = rel dim` (leaf a′ catenarity, still open).

The hypotheses are exactly the curve's: `[IsStandardSmooth k R]` (the local ring of a smooth curve —
a localization of the standard-smooth coordinate ring — supplies `Ω` finite free via
`IsStandardSmooth.free_kaehlerDifferential`) and `[FormallySmooth k (R⧸𝔪)]` (separable residue, the
(b3) δ-injectivity gate).

Route-independent foundation; certifies no challenge hole.
-/

open Algebra TensorProduct IsLocalRing

namespace Submission.CotangentInequality

universe u

variable {k R : Type u} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [Algebra.IsStandardSmooth k R] [Algebra.FormallySmooth k (R ⧸ IsLocalRing.maximalIdeal R)]

/-- **(b5)-finish, inequality half.** The conormal module `I/I²` of the residue presentation has
`finrank` (over the residue field `R⧸𝔪`) at most the rank of `Ω[R⁄k]`. -/
theorem finrank_conormal_le_finrank_kaehler :
    Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
        ((ConormalH1Cotangent.trivExt (IsLocalRing.maximalIdeal R)).Cotangent)
      ≤ Module.finrank R Ω[R⁄k] := by
  calc Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
          ((ConormalH1Cotangent.trivExt (IsLocalRing.maximalIdeal R)).Cotangent)
      ≤ Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
          ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] Ω[R⁄k]) :=
        LinearMap.finrank_le_finrank_of_injective
          (ConormalToOmega.conormal_to_omega_injective (IsLocalRing.maximalIdeal R))
    _ = Module.finrank R Ω[R⁄k] := Module.finrank_baseChange

end Submission.CotangentInequality
