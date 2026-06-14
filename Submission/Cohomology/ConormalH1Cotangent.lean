import Mathlib

/-!
# `H¹` of the cotangent complex of a quotient is the conormal module

For an ideal `I` of a commutative ring `R`, the first homology of the naive cotangent complex of
the quotient `R ⧸ I` over `R` is the conormal module `I/I²`:
`Algebra.H1Cotangent R (R ⧸ I) ≃ₗ (R ⧸ I) ⊗ I/I²` — more precisely it is the conormal module of
the *trivial* presentation `R → R → R⧸I` (polynomial-free, `Ring = R`).

This is leaf-(b) sub-brick **(b1)** of the `smooth ⇒ regular local` chain (route doc §"leaf (b)
scoped"): it is the keystone identification feeding the Jacobi–Zariski conormal sequence
`H¹(L_{κ/k}) → 𝔪/𝔪² → κ⊗Ω[R/k] → Ω[κ/k] → 0`. Route-independent (needs no smoothness or
separability): it rests only on `Algebra.Extension.H1Cotangent.equiv`, which produces an iso from
mutual `Extension.Hom`s with **no smoothness hypothesis** on either presentation.

Construction: the trivial extension `trivExt I := Extension.ofSurjective (Ideal.Quotient.mkₐ R I)`
has `Ring = R`, so its relative cotangent space `(R⧸I) ⊗_R Ω[R⁄R]` vanishes (`Ω[R⁄R]` is
subsingleton); hence its naive cotangent complex is the zero map and its `H1Cotangent` is the full
conormal `Cotangent`. The canonical polynomial presentation `Generators.self R (R⧸I)` maps to and
from `trivExt I` (forward: evaluate generators at a set-theoretic section; backward: the structure
map), so `H1Cotangent.equiv` identifies their `H1Cotangent`.
-/

open Algebra Algebra.Extension TensorProduct MvPolynomial

namespace Submission.ConormalH1Cotangent

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The trivial extension `R → R → R⧸I`: the polynomial-free presentation of the quotient with
`Ring = R` and surjection the quotient map. -/
noncomputable def trivExt : Extension R (R ⧸ I) :=
  Extension.ofSurjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective

@[simp] lemma trivExt_ker : (trivExt I).ker = I := by
  simp only [trivExt, Extension.ker, Extension.ofSurjective_Ring]
  show RingHom.ker (algebraMap R (R ⧸ I)) = I
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- The relative cotangent space of the trivial extension vanishes: it is `(R⧸I) ⊗_R Ω[R⁄R]` and
`Ω[R⁄R]` is subsingleton. -/
instance : Subsingleton ((trivExt I).CotangentSpace) := by
  have hsurj : Function.Surjective (algebraMap R R) := Function.surjective_id
  have : Subsingleton (Ω[R⁄R]) :=
    KaehlerDifferential.subsingleton_of_surjective (R := R) (S := R) hsurj
  show Subsingleton ((R ⧸ I) ⊗[R] Ω[R⁄R])
  infer_instance

/-- The canonical polynomial presentation of `R⧸I` over `R`, as an extension. -/
noncomputable abbrev genExt : Extension R (R ⧸ I) := (Generators.self R (R ⧸ I)).toExtension

set_option backward.isDefEq.respectTransparency false in
/-- Forward hom `R[X_{R⧸I}] → R`: evaluate each generator at the chosen section of the quotient. -/
noncomputable def fwd : (genExt I).Hom (trivExt I) :=
  Extension.Hom.ofAlgHom (MvPolynomial.aeval (trivExt I).σ) <| by
    refine MvPolynomial.algHom_ext (fun s => ?_)
    simp [Generators.algebraMap_apply, Generators.self_val]

/-- Backward hom `R → R[X_{R⧸I}]`: the structure map (unique `R`-algebra hom out of `R`). -/
noncomputable def bwd : (trivExt I).Hom (genExt I) :=
  Extension.Hom.ofAlgHom (Algebra.ofId R _) <| by ext

/-- **(b1)** `H¹(L_{(R⧸I)/R}) ≃ₗ` the conormal module of the trivial presentation. -/
noncomputable def h1CotangentEquivTrivCotangent :
    Algebra.H1Cotangent R (R ⧸ I) ≃ₗ[R ⧸ I] (trivExt I).Cotangent := by
  refine Extension.H1Cotangent.equiv (fwd I) (bwd I) ≪≫ₗ ?_
  -- `(trivExt I).H1Cotangent = ker cotangentComplex = ⊤`, since the codomain is subsingleton.
  have hker : LinearMap.ker (trivExt I).cotangentComplex = ⊤ := by
    rw [LinearMap.ker_eq_top]
    exact Subsingleton.elim _ _
  exact (LinearEquiv.ofEq _ _ hker) ≪≫ₗ Submodule.topEquiv

end Submission.ConormalH1Cotangent
