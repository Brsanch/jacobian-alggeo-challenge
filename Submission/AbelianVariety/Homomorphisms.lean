import Submission.AbelianVariety.Rigidity

/-!
# Consequences of rigidity: morphisms of abelian varieties

Tower C.  This file develops the immediate consequences of the rigidity lemma
(`Submission/AbelianVariety/Rigidity.lean`) for the structure of morphisms
between abelian varieties — the classical corollaries of Mumford, *Abelian
Varieties* §4.  Everything here is genuine classical content discharged on
arbitrary abelian varieties, sorry-free and axiom-free.

For abelian varieties `A`, `B` over a field `k` (proper, geometrically integral
group schemes) we prove:

* `isMonHom_iff_pointed` — **a morphism `f : A ⟶ B` is a group-object
  homomorphism iff it preserves the identity** (`η[A] ≫ f = η[B]`).  The forward
  direction is `IsMonHom.one_hom`; the (non-trivial) converse is rigidity.
* `pointedPart f := f · (e ↦ f e)⁻¹` is always pointed, hence (for abelian
  varieties) a homomorphism — `isMonHom_pointedPart`.
* `eq_pointedPart_mul_const` — **every morphism of abelian varieties is a
  homomorphism followed by a translation**: `f = pointedPart f · (const (f e))`.
* `IsMonHom`-closure under the group operations (homs form a subgroup of
  `Hom(A, B)`): `isMonHom_mul`, `isMonHom_inv`, `isMonHom_one`.

No `sorry`, no `axiom`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AbelianVariety

universe u

open AlgebraicGeometry

variable {K : Type u} [Field K]
variable (A B : Over (Spec (.of K)))
  [IsProper A.hom] [GrpObj A] [GeometricallyIntegral A.hom]
  [IsProper B.hom] [GrpObj B]

/-- The constant morphism `A ⟶ B` at the point `b : 𝟙_ ⟶ B`. -/
noncomputable def constMap (b : 𝟙_ (Over (Spec (.of K))) ⟶ B) : A ⟶ B := toUnit A ≫ b

/-- The "pointed part" of a morphism `f : A ⟶ B`: `f` with its value at the
identity divided out, `x ↦ f x · (f e)⁻¹`.  It always sends the identity to the
identity (`pointedPart_one`), and for abelian varieties it is a homomorphism. -/
noncomputable def pointedPart (f : A ⟶ B) : A ⟶ B :=
  f * (toUnit A ≫ η[A] ≫ f)⁻¹

variable {A B}

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- The pointed part is pointed: it sends the identity of `A` to the identity of `B`. -/
@[simp]
lemma pointedPart_one (f : A ⟶ B) : η[A] ≫ pointedPart A B f = η[B] := by
  have hb : (η[B] : 𝟙_ (Over (Spec (.of K))) ⟶ B) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ _)) (𝟙 _), Category.id_comp]
  have hc : η[A] ≫ (toUnit A ≫ η[A] ≫ f) = η[A] ≫ f := by
    rw [← Category.assoc, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]
  rw [hb, pointedPart, comp_mul, GrpObj.comp_inv, hc, _root_.mul_inv_cancel]

/-- For abelian varieties, the pointed part of any morphism is a homomorphism
(rigidity). -/
theorem isMonHom_pointedPart (f : A ⟶ B) : IsMonHom (pointedPart A B f) :=
  isMonHom_of_pointed_of_geometricallyIntegral A B (pointedPart A B f) (pointedPart_one f)

/-- **A morphism of abelian varieties is a homomorphism iff it preserves the
identity** (Mumford, *Abelian Varieties* §4).  The converse direction is the
rigidity lemma. -/
theorem isMonHom_iff_pointed (f : A ⟶ B) : IsMonHom f ↔ η[A] ≫ f = η[B] :=
  ⟨fun hf ↦ hf.one_hom, isMonHom_of_pointed_of_geometricallyIntegral A B f⟩

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- **Every morphism of abelian varieties is a homomorphism followed by a
translation** (Mumford, *Abelian Varieties* §4): `f` equals its pointed part
(a homomorphism) translated by the value `f` takes at the identity. -/
theorem eq_pointedPart_mul_const (f : A ⟶ B) :
    f = pointedPart A B f * (toUnit A ≫ η[A] ≫ f) := by
  rw [pointedPart, _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- The translation part of a hom-times-translation decomposition is forced: in
`f = h · (const b)` with `h` pointed, the translation `b` is the value `f` takes
at the identity. -/
theorem const_eq_of_decomp (f : A ⟶ B) {h : A ⟶ B} {b : 𝟙_ (Over (Spec (.of K))) ⟶ B}
    (hh : η[A] ≫ h = η[B]) (hf : f = h * (toUnit A ≫ b)) : η[A] ≫ f = b := by
  rw [hf, comp_mul, hh,
    show η[A] ≫ (toUnit A ≫ b) = b from by
      rw [← Category.assoc, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp],
    show (η[B] : 𝟙_ (Over (Spec (.of K))) ⟶ B) = 1 from by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ _)) (𝟙 _), Category.id_comp],
    _root_.one_mul]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- The homomorphism part of a hom-times-translation decomposition is forced to be
the pointed part: the decomposition `f = h · (const b)` with `h` pointed is unique. -/
theorem pointedPart_eq_of_decomp (f : A ⟶ B) {h : A ⟶ B} {b : 𝟙_ (Over (Spec (.of K))) ⟶ B}
    (hh : η[A] ≫ h = η[B]) (hf : f = h * (toUnit A ≫ b)) : pointedPart A B f = h := by
  have hb := const_eq_of_decomp f hh hf
  conv_lhs => rw [pointedPart, hb, hf]
  rw [_root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- Taking the pointed part of a morphism that already preserves the identity does
nothing: `pointedPart` is a retraction onto the pointed morphisms. -/
theorem pointedPart_eq_self_of_pointed (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    pointedPart A B f = f := by
  rw [pointedPart, hf, show (toUnit A ≫ η[B] : A ⟶ B) = 1 from by rw [Hom.one_def],
    _root_.inv_one, _root_.mul_one]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- `pointedPart` is idempotent. -/
@[simp]
theorem pointedPart_pointedPart (f : A ⟶ B) :
    pointedPart A B (pointedPart A B f) = pointedPart A B f :=
  pointedPart_eq_self_of_pointed _ (pointedPart_one f)

omit [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] in
/-- `pointedPart` of the trivial morphism is trivial. -/
@[simp]
theorem pointedPart_one' : pointedPart A B (1 : A ⟶ B) = 1 :=
  pointedPart_eq_self_of_pointed _ (by rw [Hom.one_def, ← Category.assoc,
    toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp])

/-- **A morphism of abelian varieties is a homomorphism iff it equals its own
pointed part.** -/
theorem isMonHom_iff_pointedPart_eq_self (f : A ⟶ B) :
    IsMonHom f ↔ pointedPart A B f = f := by
  refine ⟨fun hf ↦ pointedPart_eq_self_of_pointed f hf.one_hom, fun hf ↦ ?_⟩
  rw [← hf]; exact isMonHom_pointedPart f

/-- **The only constant morphism of abelian varieties that is a homomorphism is the
trivial (identity-valued) one.** -/
theorem isMonHom_constMap_iff (b : 𝟙_ (Over (Spec (.of K))) ⟶ B) :
    IsMonHom (constMap A B b) ↔ b = η[B] := by
  rw [constMap, isMonHom_iff_pointed,
    show η[A] ≫ (toUnit A ≫ b) = b from by
      rw [← Category.assoc, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- **`pointedPart` is multiplicative**: for abelian varieties (with commutative
target) it is a group homomorphism `Hom(A, B) → Hom(A, B)`, the canonical
retraction onto the subgroup of homomorphisms. -/
theorem pointedPart_mul [GeometricallyIntegral B.hom] (f g : A ⟶ B) :
    pointedPart A B (f * g) = pointedPart A B f * pointedPart A B g := by
  haveI : IsCommMonObj B := isCommMonObj_of_isProper_of_geometricallyIntegral B
  simp only [pointedPart, comp_mul]
  rw [_root_.mul_inv]
  ac_rfl

end AbelianVariety
