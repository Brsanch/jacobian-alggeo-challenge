import Mathlib

/-!
# Jacobi–Zariski: the connecting map `δ` is injective when the base→residue `H¹` vanishes

For a tower of algebras `k → R → κ`, the Jacobi–Zariski connecting homomorphism
`δ : H¹(L_{κ/R}) → κ ⊗_R Ω[R⁄k]` is **injective** as soon as `H¹(L_{κ/k})` is subsingleton.

This is leaf-(b) sub-brick **(b3)** of the `smooth ⇒ regular local` chain (route doc §"leaf (b)
scoped"). It is the precise content of the **separability gate**: by the J-Z exactness
`H¹(L_{κ/k}) →[map] H¹(L_{κ/R}) →[δ] κ⊗_R Ω[R⁄k]` (`Algebra.H1Cotangent.exact_map_δ`), one has
`ker δ = range map`; when `H¹(L_{κ/k})` is subsingleton the connecting `map` is the zero map, so
`ker δ = ⊥` and `δ` is injective. Composed with brick **(b1)**
(`Algebra.H1Cotangent R κ ≃ₗ 𝔪/𝔪²`, `ConormalH1Cotangent`), this makes the cotangent/conormal map
`𝔪/𝔪² → κ ⊗_R Ω[R⁄k]` injective — the inequality `embed dim ≤ …` driving regularity.

`H¹(L_{κ/k}) = Algebra.H1Cotangent k κ` is subsingleton precisely when `κ` is **formally smooth**
over `k` (`Algebra.FormallySmooth.subsingleton_h1Cotangent`), which for a residue-field extension
holds when `κ/k` is **separable** (`Algebra.FormallyEtale.of_isSeparable`, étale ⟹ smooth) — the
clean separable-residue case. The inseparable case is the genuine wall (the J-Z left exactness that
would still force `map = 0` is not exposed at the pin; see route doc §"leaf (b) scoped" (b3)).

Route-independent foundation; certifies no challenge hole.
-/

open Algebra TensorProduct

namespace Submission.CotangentDeltaInjective

universe u

variable {k R κ : Type u} [CommRing k] [CommRing R] [CommRing κ]
  [Algebra k R] [Algebra R κ] [Algebra k κ] [IsScalarTower k R κ]

/-- **(b3)** For a tower `k → R → κ`, if `H¹(L_{κ/k})` is subsingleton then the Jacobi–Zariski
connecting map `δ : H¹(L_{κ/R}) → κ ⊗_R Ω[R⁄k]` is injective. -/
theorem δ_injective_of_h1Cotangent_subsingleton
    (h : Subsingleton (Algebra.H1Cotangent k κ)) :
    Function.Injective (Algebra.H1Cotangent.δ k R κ) := by
  haveI := h
  rw [← LinearMap.ker_eq_bot, (Algebra.H1Cotangent.exact_map_δ k R κ).linearMap_ker_eq,
    LinearMap.range_eq_bot]
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- **(b3), separable-residue form.** If `κ` is formally smooth over `k` (e.g. `κ/k` a separable
residue-field extension), the Jacobi–Zariski connecting map `δ : H¹(L_{κ/R}) → κ ⊗_R Ω[R⁄k]` is
injective. -/
theorem δ_injective_of_formallySmooth_residue [Algebra.FormallySmooth k κ] :
    Function.Injective (Algebra.H1Cotangent.δ k R κ) :=
  δ_injective_of_h1Cotangent_subsingleton Algebra.FormallySmooth.subsingleton_h1Cotangent

end Submission.CotangentDeltaInjective
