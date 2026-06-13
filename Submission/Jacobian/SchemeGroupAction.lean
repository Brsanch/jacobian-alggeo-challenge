import Submission.Jacobian.AffineQuotient

/-!
# Functoriality of the `G`-action on `Spec B`

The maps `specAction g : Spec B → Spec B` (`AffineQuotient.specAction`) assemble into a genuine
action of `G` on the affine scheme `Spec B`, lifted contravariantly from the `MulSemiringAction`
on `B`:

* `specAction_one` — `specAction 1 = 𝟙`;
* `specAction_mul` — `specAction (g * h) = specAction g ≫ specAction h` (the contravariant
  composition law);
* `specAction_isIso` — each `specAction g` is an isomorphism (with inverse `specAction g⁻¹`).

Together with `AffineQuotient.specAction_comp_quotientMap`, these say the quotient map
`π : Spec B → Spec(B^G)` is a genuine `G`-invariant morphism for a genuine `G`-action.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.JacobianChallenge.AffineQuotient

universe u v

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (G : Type v) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

@[simp] theorem specAction_one :
    specAction R B G (1 : G) = 𝟙 (Spec (CommRingCat.of B)) := by
  have h1 : MulSemiringAction.toRingHom G B (1 : G) = RingHom.id B := by
    ext b
    simp only [MulSemiringAction.toRingHom_apply, one_smul, RingHom.id_apply]
  rw [specAction, h1, CommRingCat.ofHom_id, Spec.map_id]

theorem specAction_mul (g h : G) :
    specAction R B G (g * h) = specAction R B G g ≫ specAction R B G h := by
  have hm : MulSemiringAction.toRingHom G B (g * h)
      = (MulSemiringAction.toRingHom G B g).comp (MulSemiringAction.toRingHom G B h) := by
    ext b
    simp only [MulSemiringAction.toRingHom_apply, RingHom.comp_apply, mul_smul]
  simp only [specAction]
  rw [hm, CommRingCat.ofHom_comp, Spec.map_comp]

/-- `specAction g` and `specAction g⁻¹` are mutually inverse. -/
@[simp] theorem specAction_comp_inv (g : G) :
    specAction R B G g ≫ specAction R B G g⁻¹ = 𝟙 (Spec (CommRingCat.of B)) := by
  rw [← specAction_mul, mul_inv_cancel, specAction_one]

@[simp] theorem specAction_inv_comp (g : G) :
    specAction R B G g⁻¹ ≫ specAction R B G g = 𝟙 (Spec (CommRingCat.of B)) := by
  rw [← specAction_mul, inv_mul_cancel, specAction_one]

/-- Each `specAction g` is an isomorphism of `Spec B`. -/
instance specAction_isIso (g : G) : IsIso (specAction R B G g) :=
  ⟨specAction R B G g⁻¹, specAction_comp_inv R B G g, specAction_inv_comp R B G g⟩

end AlgebraicGeometry.JacobianChallenge.AffineQuotient
