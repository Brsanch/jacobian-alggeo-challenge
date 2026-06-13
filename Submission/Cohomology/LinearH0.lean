import Mathlib

/-!
# Linear refinements of the adjunction additivity lemmas (Tower A foundation, fork-II)

For an adjunction `F ⊣ G` between `R`-linear functors of `R`-linear categories, the
hom-set bijection and the adjoint functors are `R`-**linear**. mathlib has only the additive
versions (`Adjunction.homAddEquiv`, `right_/left_adjoint_additive`); these are the
`Functor.Linear` analogues, verified absent at the pin by compile-probe (2026-06-13).

These are the general lemmas underlying the `k`-linear upgrade of Segment 1's additive
`HZeroAddEquivΓ` — the upgrade is needed because `FiniteDimensional k` does not transport
along a mere `AddEquiv` when `k` is infinite. They are self-contained and upstreamable to
mathlib as-is (fork II); wiring them to the curve's `H⁰` (and thence to genus finiteness)
additionally requires Serre finiteness, which is the open Tower-A wall.

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {R : Type*} [Semiring R]
variable {C : Type*} [Category C] {D : Type*} [Category D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C}

-- An adjoint on the right of an `R`-linear functor is `R`-linear
-- (the `Linear` analogue of `Adjunction.right_adjoint_additive`).
set_option backward.isDefEq.respectTransparency false in
lemma right_adjoint_linear (adj : F ⊣ G) [F.Linear R] : G.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

-- An adjoint on the left of an `R`-linear functor is `R`-linear
-- (the `Linear` analogue of `Adjunction.left_adjoint_additive`).
set_option backward.isDefEq.respectTransparency false in
lemma left_adjoint_linear (adj : F ⊣ G) [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

variable (adj : F ⊣ G) [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]

/-- The hom-set bijection of an adjunction between `R`-linear functors is `R`-linear
(the `Linear` analogue of `Adjunction.homAddEquiv`). -/
noncomputable def homLinearEquiv (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  (adj.homAddEquiv X Y).toLinearEquiv (fun r f => by
    simp [Adjunction.homAddEquiv_apply, Adjunction.homEquiv_unit, Functor.map_smul])

@[simp]
lemma homLinearEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv (R := R) X Y f = adj.homEquiv X Y f := rfl

@[simp]
lemma homLinearEquiv_symm_apply (X : C) (Y : D) (g : X ⟶ G.obj Y) :
    (adj.homLinearEquiv (R := R) X Y).symm g = (adj.homEquiv X Y).symm g := rfl

end CategoryTheory.Adjunction
