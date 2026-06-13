import Submission.Jacobian.InvariantFiniteness

/-!
# Invariant-ring lemmas for the affine finite-group quotient

Characterizes the invariant subalgebra `B^G = FixedPoints.subalgebra R B G` as the
*equalizer of the `G`-action*: `b ∈ B^G ↔ ∀ g, g • b = b`. This is the ring-side heart of
the categorical-quotient universal property of `Spec(B^G)` — a ring map `R' →+* B` that is
`G`-invariant (lands in the fixed points) is the same as a ring map `R' →+* B^G`.

All content is about genuine objects (`FixedPoints.subalgebra`, the structure map); there
are no `True`-valued fields. Route-independent invariant theory; consumed by the affine
quotient module (`Submission/Jacobian/AffineQuotient.lean`).
-/

namespace AlgebraicGeometry.JacobianChallenge.AffineQuotient

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- Membership in the invariant subalgebra is exactly `G`-invariance. -/
theorem mem_fixedPoints_subalgebra {b : B} :
    b ∈ FixedPoints.subalgebra R B G ↔ ∀ g : G, g • b = b := Iff.rfl

/-- An element of the invariant subalgebra is fixed by the action (as an element of `B`). -/
@[simp] theorem smul_coe_fixedPoints (a : FixedPoints.subalgebra R B G) (g : G) :
    g • (a : B) = (a : B) := a.2 g

/-- The structure map `B^G → B` lands in the fixed points: it is `G`-invariant. -/
theorem smul_algebraMap_fixedPoints (a : FixedPoints.subalgebra R B G) (g : G) :
    g • algebraMap (FixedPoints.subalgebra R B G) B a = algebraMap (FixedPoints.subalgebra R B G) B a :=
  a.2 g

/-- The inclusion `B^G ↪ B` is injective. -/
theorem algebraMap_fixedPoints_injective :
    Function.Injective (algebraMap (FixedPoints.subalgebra R B G) B) :=
  Subtype.val_injective

/-- **Equalizer characterization.** A `G`-invariant element of `B` (fixed by every `g`) is
exactly an element of the image of `B^G`; equivalently `B^G` is the equalizer of the two
maps `B ⇉ (G → B)`, `b ↦ (g ↦ g • b)` and `b ↦ (g ↦ b)`. -/
theorem isInvariant_iff_mem {b : B} :
    (∀ g : G, g • b = b) ↔ ∃ a : FixedPoints.subalgebra R B G, (a : B) = b :=
  ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ g => ha ▸ a.2 g⟩

/-- Universal factorization at the ring level: a ring hom `f : R' →+* B` whose image is
`G`-invariant factors (uniquely, by injectivity of the inclusion) through `B^G`. This is the
affine categorical-quotient property, ring-side. -/
theorem exists_lift_of_invariant {R' : Type*} [CommRing R'] (f : R' →+* B)
    (hf : ∀ (g : G) (x : R'), g • f x = f x) :
    ∃ f' : R' →+* FixedPoints.subalgebra R B G,
      (algebraMap (FixedPoints.subalgebra R B G) B).comp f' = f := by
  refine ⟨{ toFun := fun x => ⟨f x, fun g => hf g x⟩
            map_one' := by ext; simp
            map_mul' := by intro x y; ext; simp
            map_zero' := by ext; simp
            map_add' := by intro x y; ext; simp }, ?_⟩
  ext x
  rfl

end AlgebraicGeometry.JacobianChallenge.AffineQuotient
