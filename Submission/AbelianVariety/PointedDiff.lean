import Mathlib

/-!
# The pointed-difference map and the homomorphism criterion

Tower C (abelian-variety theory).  This is the **categorical** half of the
"pointed morphisms of abelian varieties are homomorphisms" result that hole 9
(`exists_unique_ofCurve_comp`) consumes.  It is the exact companion to mathlib's
`CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_η`: it reduces the
homomorphism property of a *pointed* map `h : A ⟶ B` (a map sending the unit to
the unit) to the **constancy** of a single morphism `pointedDiff h : A ⊗ A ⟶ B`,
namely `(x, y) ↦ h (x * y) * (h x * h y)⁻¹`.

The geometric input — that this map *is* constant when `A` is a complete
(proper, geometrically irreducible) variety — is the rigidity lemma, supplied
separately (`Submission/AbelianVariety/Rigidity.lean`).  Here we prove, in any
cartesian-monoidal category, purely formally:

* `isMonHom_iff_pointedDiff_eq` — for a pointed `h`, `IsMonHom h` iff
  `pointedDiff h = toUnit _ ≫ η` (the constant map at the unit of `B`);
* `lift_id_one_pointedDiff` / `lift_one_id_pointedDiff` — `pointedDiff h`
  restricted to either "axis" `A × {e}` or `{e} × A` is the constant unit.

No `sorry`, no `axiom`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AbelianVariety

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B : C} [MonObj A] [GrpObj B]

/-- The **pointed-difference map** of `h : A ⟶ B`, measuring the failure of `h`
to be a homomorphism: informally `(x, y) ↦ h (x * y) * (h x * h y)⁻¹`.

It is the unit of the group `Hom(A ⊗ A, B)` exactly when `h` is multiplicative,
see `pointedDiff_eq_toUnit_η_iff`. -/
noncomputable def pointedDiff (h : A ⟶ B) : A ⊗ A ⟶ B :=
  (μ[A] ≫ h) * ((fst A A ≫ h) * (snd A A ≫ h))⁻¹

omit [MonObj A] in
/-- `h ⊗ₘ h` followed by the multiplication of `B` is the product, in the group
`Hom(A ⊗ A, B)`, of `h` on the two projections. -/
lemma tensorHom_comp_mul (h : A ⟶ B) :
    (h ⊗ₘ h) ≫ μ[B] = (fst A A ≫ h) * (snd A A ≫ h) := by
  rw [Hom.mul_def]
  congr 1
  ext <;> simp [tensorHom_fst, tensorHom_snd]

/-- The multiplicative part of `IsMonHom h` written with the projections. -/
lemma pointedDiff_eq_toUnit_η_iff (h : A ⟶ B) :
    pointedDiff h = toUnit _ ≫ η ↔ μ[A] ≫ h = (h ⊗ₘ h) ≫ μ[B] := by
  rw [pointedDiff, tensorHom_comp_mul, ← Hom.one_def, mul_inv_eq_one]

/-- **Homomorphism criterion.**  A *pointed* morphism `h : A ⟶ B`
(i.e. `η[A] ≫ h = η[B]`) is a monoid-object homomorphism iff its
pointed-difference map is the constant unit. -/
lemma isMonHom_iff_pointedDiff_eq (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    IsMonHom h ↔ pointedDiff h = toUnit _ ≫ η := by
  rw [pointedDiff_eq_toUnit_η_iff]
  constructor
  · intro hh; exact hh.mul_hom
  · intro hmul; exact ⟨hone, hmul⟩

/-- `pointedDiff h` restricted to the axis `A × {e}` (the map `x ↦ (x, e)`) is
the constant unit, provided `h` is pointed. -/
lemma lift_id_one_pointedDiff (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    lift (𝟙 A) (toUnit A ≫ η) ≫ pointedDiff h = toUnit _ ≫ η := by
  rw [pointedDiff, comp_mul, GrpObj.comp_inv, comp_mul]
  have e1 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (μ[A] ≫ h) = h := by
    rw [← Category.assoc, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, Category.id_comp]
  have e2 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (fst A A ≫ h) = h := by
    rw [← Category.assoc, lift_fst, Category.id_comp]
  have e3 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (snd A A ≫ h) = toUnit _ ≫ η := by
    rw [← Category.assoc, lift_snd, Category.assoc, hone]
  rw [e1, e2, e3, ← Hom.one_def, _root_.mul_one, _root_.mul_inv_cancel]

/-- `pointedDiff h` restricted to the axis `{e} × A` (the map `y ↦ (e, y)`) is
the constant unit, provided `h` is pointed. -/
lemma lift_one_id_pointedDiff (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    lift (toUnit A ≫ η) (𝟙 A) ≫ pointedDiff h = toUnit _ ≫ η := by
  rw [pointedDiff, comp_mul, GrpObj.comp_inv, comp_mul]
  have e1 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (μ[A] ≫ h) = h := by
    rw [← Category.assoc, ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, Category.id_comp]
  have e2 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (fst A A ≫ h) = toUnit _ ≫ η := by
    rw [← Category.assoc, lift_fst, Category.assoc, hone]
  have e3 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (snd A A ≫ h) = h := by
    rw [← Category.assoc, lift_snd, Category.id_comp]
  rw [e1, e2, e3, ← Hom.one_def, _root_.one_mul, _root_.mul_inv_cancel]

/-- General `{e} × A` axis vanishing: precomposing `pointedDiff h` with the
map `(e, g·) : X ⟶ A ⊗ A` (first coordinate the unit) yields the constant unit,
provided `h` is pointed.  Specialises both `lift_one_id_pointedDiff` (`X = A`,
`g = 𝟙`) and `lift_unit_pointedDiff` (`X = 𝟙_`). -/
lemma lift_one_comp_pointedDiff (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) {X : C} (g : X ⟶ A) :
    lift (toUnit X ≫ η) g ≫ pointedDiff h = toUnit _ ≫ η := by
  rw [pointedDiff, comp_mul, GrpObj.comp_inv, comp_mul]
  have e1 : lift (toUnit X ≫ η[A]) g ≫ (μ[A] ≫ h) = g ≫ h := by
    rw [← Category.assoc, ← Hom.mul_def, ← Hom.one_def, _root_.one_mul]
  have e2 : lift (toUnit X ≫ η[A]) g ≫ (fst A A ≫ h) = toUnit _ ≫ η := by
    rw [← Category.assoc, lift_fst, Category.assoc, hone]
  have e3 : lift (toUnit X ≫ η[A]) g ≫ (snd A A ≫ h) = g ≫ h := by
    rw [← Category.assoc, lift_snd]
  rw [e1, e2, e3, ← Hom.one_def, _root_.one_mul, _root_.mul_inv_cancel]

/-- `{e} × A` axis vanishing over the monoidal unit: for any `g : 𝟙_ ⟶ A`,
`lift η[A] g ≫ pointedDiff h = η[B]`, provided `h` is pointed.  This is the
form Mumford's rigidity argument consumes on closed `K`-points. -/
lemma lift_unit_pointedDiff (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) (g : 𝟙_ C ⟶ A) :
    lift η[A] g ≫ pointedDiff h = η[B] := by
  have key := lift_one_comp_pointedDiff h hone g
  simpa only [toUnit_unique (toUnit (𝟙_ C)) (𝟙 _), Category.id_comp] using key

/-- `A × {e}` axis vanishing in whiskering form: `A ◁ η[A] ≫ pointedDiff h` is the
constant unit, provided `h` is pointed.  Analog of mathlib's
`GrpObj.whiskerLeft_η_commutator`; this is the form the rigidity argument's
fibre-constancy step consumes. -/
lemma whiskerLeft_η_pointedDiff (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    A ◁ η[A] ≫ pointedDiff h = toUnit _ ≫ η := by
  have e : A ◁ η[A] = (ρ_ A).hom ≫ lift (𝟙 A) (toUnit A ≫ η[A]) := by
    ext <;> simp [rightUnitor_hom, toUnit_unique (snd A (𝟙_ C)) (toUnit (A ⊗ 𝟙_ C))]
  rw [e, Category.assoc, lift_id_one_pointedDiff h hone]
  simp

end AbelianVariety
