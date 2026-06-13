import Submission.Jacobian.InvariantFiniteness
import Submission.Jacobian.AffineInvariants

/-!
# The affine finite-group quotient `Spec(B^G)` of `Spec B`

For a finite group `G` acting by `R`-algebra automorphisms on a finite-type `R`-algebra `B`,
this file builds the affine quotient scheme `Spec(B^G)` and the quotient morphism
`π : Spec B → Spec(B^G)`, and proves its defining properties:

* `quotientMap_isIntegralHom` — `π` is an integral morphism (hence `UniversallyClosed`);
* `quotientMap_finite` — `π` is finite (hence `IsProper`, `IsAffineHom`) when `B` is of
  finite type over `R` (uses Noether finiteness, `InvariantFiniteness`);
* `specAction_comp_quotientMap` — `π` is `G`-invariant: `g̃ ≫ π = π` for every `g`;
* `exists_unique_lift_of_invariant` — the **categorical-quotient universal property** for
  affine targets: a `G`-invariant morphism `Spec B → Spec R'` factors uniquely through `π`.

This is the affine building block (route-doc milestone M3) of the finite-group quotient
`Sym^d C = C^d/S_d`. The `Scheme` category has no coequalizers, so the quotient is built by
hand via `Spec` of the invariant subalgebra; the universal property is proved through the
`Γ ⊣ Spec` adjunction (`Spec.map_injective`, fully-faithfulness of `Spec`). Route-independent,
mathlib-PR-shaped; not a Route-A commitment.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.JacobianChallenge.AffineQuotient

universe u v

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (G : Type v) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The invariant subalgebra `B^G`, as an object of `CommRingCat`. -/
abbrev invariantRing : CommRingCat.{u} := CommRingCat.of (FixedPoints.subalgebra R B G)

/-- The inclusion `B^G ↪ B`, as a morphism of `CommRingCat`. -/
noncomputable def inclHom : invariantRing R B G ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B)

/-- The affine quotient scheme `Spec(B^G)`. -/
noncomputable def affineQuotient : Scheme.{u} := Spec (invariantRing R B G)

/-- The quotient morphism `π : Spec B → Spec(B^G)`, dual to the inclusion `B^G ↪ B`. -/
noncomputable def quotientMap : Spec (CommRingCat.of B) ⟶ affineQuotient R B G :=
  Spec.map (inclHom R B G)

/-- The automorphism of `Spec B` induced by `g : G` (contravariant `Spec` of `g`'s ring
automorphism). This is the `G`-action on `Spec B` lifted from the action on `B`. -/
noncomputable def specAction (R B : Type u) (G : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G R B] (g : G) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g))

/-- `π` is an integral morphism: `B` is integral over `B^G` for finite `G`. -/
theorem quotientMap_isIntegralHom [Finite G] : IsIntegralHom (quotientMap R B G) := by
  have h : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B :=
    InvariantFiniteness.isIntegral_fixedPoints R B G
  rw [quotientMap, inclHom]
  exact IsIntegralHom.SpecMap_iff.mpr (Algebra.IsIntegral.isIntegral (R := FixedPoints.subalgebra R B G))

/-- `π` is universally closed (integral morphisms are). -/
instance instUniversallyClosed [Finite G] : UniversallyClosed (quotientMap R B G) :=
  have := quotientMap_isIntegralHom R B G
  inferInstance

/-- `π` is a finite morphism when `B` is of finite type over `R` (Noether finiteness:
`B` is module-finite over `B^G`). -/
theorem quotientMap_finite [Finite G] [Algebra.FiniteType R B] :
    IsFinite (quotientMap R B G) := by
  have hfin : Module.Finite (FixedPoints.subalgebra R B G) B :=
    InvariantFiniteness.moduleFinite_of_finiteType R B G
  rw [quotientMap, inclHom]
  refine (IsFinite.SpecMap_iff _).mpr ?_
  rw [RingHom.Finite]
  exact hfin

/-- `π` is proper (finite morphisms are proper). -/
theorem quotientMap_isProper [Finite G] [Algebra.FiniteType R B] :
    IsProper (quotientMap R B G) :=
  have := quotientMap_finite R B G
  inferInstance

/-- **`π` is `G`-invariant**: `g̃ ≫ π = π` for every `g : G`. The composite dualizes to the
ring map `B^G → B`, `a ↦ g • a`, which is just the inclusion since `B^G` is fixed. -/
theorem specAction_comp_quotientMap (g : G) :
    specAction R B G g ≫ quotientMap R B G = quotientMap R B G := by
  have hring : inclHom R B G ≫ CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)
      = inclHom R B G := by
    rw [inclHom]
    apply CommRingCat.hom_ext
    ext a
    exact a.2 g
  rw [specAction, quotientMap]
  calc Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) ≫ Spec.map (inclHom R B G)
      = Spec.map (inclHom R B G ≫ CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) :=
        (Spec.map_comp _ _).symm
    _ = Spec.map (inclHom R B G) := by rw [hring]

/-- **Affine categorical-quotient universal property.** A morphism `Spec B → Spec R'` whose
dual ring map `φ : R' → B` has `G`-fixed image factors *uniquely* through the quotient
`π : Spec B → Spec(B^G)`. -/
theorem exists_unique_lift_of_invariant {R' : Type u} [CommRing R']
    (φ : CommRingCat.of R' ⟶ CommRingCat.of B)
    (hφ : ∀ (g : G) (x : R'), g • φ.hom x = φ.hom x) :
    ∃! ψ : affineQuotient R B G ⟶ Spec (CommRingCat.of R'),
      quotientMap R B G ≫ ψ = Spec.map φ := by
  obtain ⟨φ', hφ'⟩ :=
    AffineQuotient.exists_lift_of_invariant R B G φ.hom hφ
  -- `hφ' : (algebraMap (B^G) B).comp φ' = φ.hom`, i.e. `ofHom φ' ≫ inclHom = φ`.
  have key : CommRingCat.ofHom φ' ≫ inclHom R B G = φ := by
    rw [inclHom]; apply CommRingCat.hom_ext; exact hφ'
  refine ⟨Spec.map (CommRingCat.ofHom φ'), ?_, ?_⟩
  · show quotientMap R B G ≫ Spec.map (CommRingCat.ofHom φ') = Spec.map φ
    rw [quotientMap]
    calc Spec.map (inclHom R B G) ≫ Spec.map (CommRingCat.ofHom φ')
        = Spec.map (CommRingCat.ofHom φ' ≫ inclHom R B G) := (Spec.map_comp _ _).symm
      _ = Spec.map φ := by rw [key]
  · intro ψ hψ
    obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
    rw [quotientMap] at hψ
    have hχ : χ ≫ inclHom R B G = φ := by
      apply Spec.map_injective
      calc Spec.map (χ ≫ inclHom R B G)
          = Spec.map (inclHom R B G) ≫ Spec.map χ := Spec.map_comp _ _
        _ = Spec.map φ := hψ
    have heq : χ ≫ inclHom R B G = CommRingCat.ofHom φ' ≫ inclHom R B G := by rw [hχ, key]
    have hfinal : χ = CommRingCat.ofHom φ' := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      apply algebraMap_fixedPoints_injective R B G
      have h2 := congrArg (fun m => (CommRingCat.Hom.hom m) x) heq
      simpa [inclHom] using h2
    rw [hfinal]

end AlgebraicGeometry.JacobianChallenge.AffineQuotient
