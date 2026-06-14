import Mathlib
import Submission.Cohomology.ConormalH1Cotangent
import Submission.Cohomology.CotangentDeltaInjective

/-!
# The conormal module injects into `κ ⊗ Ω[R⁄k]` (separable residue)

Composing brick **(b1)** (`Algebra.H1Cotangent R (R⧸I) ≃ₗ` the conormal `I/I²`, `ConormalH1Cotangent`)
with brick **(b3)** (the Jacobi–Zariski `δ` is injective when the base→residue `H¹` vanishes,
`CotangentDeltaInjective`): for a tower `k → R → R⧸I` with `R⧸I` formally smooth over `k`, the
conormal-to-differentials map

`(trivExt I).Cotangent  →[δ ∘ equiv.symm]  (R⧸I) ⊗_R Ω[R⁄k]`

is **injective**. Specialized to `I = 𝔪` of a local ring with separable residue field, this is the
cotangent injection `𝔪/𝔪² ↪ κ ⊗_R Ω[R⁄k]` — the inequality `embed dim ≤ rank Ω` that drives
`smooth ⇒ regular` (leaf-(b), route doc §"leaf (b) scoped", the (b5)-assembly core). The bound
`finrank_κ(𝔪/𝔪²) ≤ finrank_κ(κ⊗Ω) = rank_R Ω[R⁄k] = rel dim` then follows from finiteness of `Ω`
(mathlib for `IsStandardSmooth`: `free_kaehlerDifferential` + `rank_kaehlerDifferential`).

Route-independent foundation; certifies no challenge hole.
-/

open Algebra TensorProduct

namespace Submission.ConormalToOmega

universe u

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
  [Algebra.FormallySmooth k (R ⧸ I)]

/-- **(b5)-core.** For a tower `k → R → R⧸I` with `R⧸I` formally smooth over `k`, the conormal
module `I/I²` (`= (trivExt I).Cotangent`, brick (b1)) injects into `(R⧸I) ⊗_R Ω[R⁄k]` via the
Jacobi–Zariski connecting map `δ` (injective by brick (b3)) precomposed with the (b1) isomorphism.
Specialized to `I = 𝔪` with separable residue field, this is `𝔪/𝔪² ↪ κ ⊗_R Ω[R⁄k]`. -/
theorem conormal_to_omega_injective :
    Function.Injective
      ((Algebra.H1Cotangent.δ k R (R ⧸ I)).comp
        (ConormalH1Cotangent.h1CotangentEquivTrivCotangent I).symm.toLinearMap) := by
  rw [LinearMap.coe_comp]
  exact CotangentDeltaInjective.δ_injective_of_formallySmooth_residue.comp
    (ConormalH1Cotangent.h1CotangentEquivTrivCotangent I).symm.injective

end Submission.ConormalToOmega
