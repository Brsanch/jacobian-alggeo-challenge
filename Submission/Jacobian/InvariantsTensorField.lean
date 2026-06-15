import Submission.Jacobian.TensorOverFieldInjective

/-!
# Invariants commute with tensoring over a field (the char-free core of brick (c-ii))

For the affine addition map `Sym^d × Sym^e → Sym^{d+e}` (the algebraic heart of the group law,
hole 3) we must know that the equivariant image of brick (b) — landing in the `(S_d × S_e)`-invariants
of `A^{⊗d} ⊗ A^{⊗e}` — is exactly the image of `(A^{⊗d})^{S_d} ⊗ (A^{⊗e})^{S_e}`. The substantive
content is **invariants commute with `⊗` over a field**:
```
(N ⊗_k M)^G  ≅  N ⊗_k M^G        (G acting on N ⊗ M through the M-factor)
```
for a field `k`, a finite group `G` acting `k`-linearly on `M`, and an arbitrary `k`-module `N`.

This is **char-free**: the challenge curve lives over an arbitrary field `k`, so `char k` may divide
`d! = |S_d|`, making the Reynolds/averaging projector (`Representation.averageMap`, which needs
`[Invertible (Fintype.card G : k)]`) unavailable. The correct route is **flatness/exactness**: over a
field every module is flat, and flat base change commutes with equalizers, hence with invariants.

The mechanism, following the route doc `docs/ROUTE_ADDITION_MAP_INVARIANTS_2026_06_14.md`:

* `M^G` is the equalizer `eqLocus δ c` of `δ m = (g ↦ g • m)` and `c m = (g ↦ m)`
  (`invDelta`, `invConst`).
* The `G`-action on `N ⊗ M` (through the `M`-factor) has its invariants `eqLocus δ' c'`
  (`invDelta'`, `invConst'`), `δ' x = (g ↦ (g • ·).lTensor x)`.
* `LinearMap.tensorEqLocusEquiv` (flat base change commutes with the equalizer):
  `N ⊗ eqLocus(δ, c) ≃ eqLocus(N ⊗ δ, N ⊗ c)`.
* `TensorProduct.piRight : N ⊗ (G → M) ≃ (G → N ⊗ M)` intertwines `lTensor N δ` with `δ'`
  (`piRight_lTensor_invDelta_apply`), so `eqLocus(N ⊗ δ, N ⊗ c) = (N ⊗ M)^G`.

Composing gives `invariantsTensorEquiv : N ⊗_k M^G ≃ₗ[k] (N ⊗_k M)^G`. Obligations (1)–(4) of the
route. Route-independent, mathlib-PR-shaped.
-/

set_option maxHeartbeats 1000000

open scoped TensorProduct
open LinearMap

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

section Core

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Fintype G] [DecidableEq G]
variable (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
variable (N : Type u) [AddCommGroup N] [Module k N]

/-- `δ : M →ₗ[k] (G → M)`, `m ↦ (g ↦ g • m)`. (`k`-linear because `G` acts `k`-linearly.) -/
def invDelta : M →ₗ[k] (G → M) := LinearMap.pi fun g => DistribSMul.toLinearMap k M g

/-- `c : M →ₗ[k] (G → M)`, `m ↦ (g ↦ m)` (constant). -/
def invConst : M →ₗ[k] (G → M) := LinearMap.pi fun _ => LinearMap.id

@[simp] theorem invDelta_apply (m : M) (g : G) : invDelta k G M m g = g • m := rfl
@[simp] theorem invConst_apply (m : M) (g : G) : invConst k G M m g = m := rfl

/-- The fixed-point submodule `M^G = {m | ∀ g, g • m = m}`, as the equalizer of `δ` and `c`. -/
def invariantSubmodule : Submodule k M := LinearMap.eqLocus (invDelta k G M) (invConst k G M)

theorem mem_invariantSubmodule {m : M} :
    m ∈ invariantSubmodule k G M ↔ ∀ g : G, g • m = m := by
  simp only [invariantSubmodule, LinearMap.mem_eqLocus]
  constructor
  · intro h g; exact congrFun h g
  · intro h; funext g; exact h g

/-- `δ' : N ⊗ M →ₗ[k] (G → N ⊗ M)`, the diagonal `G`-action (through the `M`-factor) packaged:
`x ↦ (g ↦ (g • ·).lTensor x)`. -/
def invDelta' : (N ⊗[k] M) →ₗ[k] (G → N ⊗[k] M) :=
  LinearMap.pi fun g => LinearMap.lTensor N (DistribSMul.toLinearMap k M g)

/-- `c' : N ⊗ M →ₗ[k] (G → N ⊗ M)`, the constant map. -/
def invConst' : (N ⊗[k] M) →ₗ[k] (G → N ⊗[k] M) := LinearMap.pi fun _ => LinearMap.id

/-- The fixed-point submodule `(N ⊗ M)^G` of the diagonal action. -/
def tensorInvariantSubmodule : Submodule k (N ⊗[k] M) :=
  LinearMap.eqLocus (invDelta' k G M N) (invConst' k G M N)

theorem mem_tensorInvariantSubmodule {x : N ⊗[k] M} :
    x ∈ tensorInvariantSubmodule k G M N
      ↔ ∀ g : G, LinearMap.lTensor N (DistribSMul.toLinearMap k M g) x = x := by
  simp only [tensorInvariantSubmodule, LinearMap.mem_eqLocus]
  constructor
  · intro h g
    have := congrFun h g
    simpa only [invDelta', invConst', LinearMap.pi_apply, LinearMap.id_coe, id_eq] using this
  · intro h
    funext g
    simpa only [invDelta', invConst', LinearMap.pi_apply, LinearMap.id_coe, id_eq] using h g

/-- **Naturality (the fiddly step).** `piRight` intertwines `lTensor N δ` with `δ'`. -/
theorem piRight_lTensor_invDelta_apply (x : N ⊗[k] M) :
    (TensorProduct.piRight k k N fun _ : G => M) (LinearMap.lTensor N (invDelta k G M) x)
      = invDelta' k G M N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n m =>
    funext g
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      invDelta_apply, invDelta', LinearMap.pi_apply, DistribSMul.toLinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Naturality.** `piRight` intertwines `lTensor N c` with `c'`. -/
theorem piRight_lTensor_invConst_apply (x : N ⊗[k] M) :
    (TensorProduct.piRight k k N fun _ : G => M) (LinearMap.lTensor N (invConst k G M) x)
      = invConst' k G M N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n m =>
    funext g
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      invConst_apply, invConst', LinearMap.pi_apply, LinearMap.id_coe, id_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The equalizer of the `lTensor`ed maps is exactly the diagonal invariants `(N ⊗ M)^G`
(matching via `piRight`, which is injective). -/
theorem tensorInvariantSubmodule_eq :
    LinearMap.eqLocus (LinearMap.lTensor N (invDelta k G M)) (LinearMap.lTensor N (invConst k G M))
      = tensorInvariantSubmodule k G M N := by
  ext x
  simp only [tensorInvariantSubmodule, LinearMap.mem_eqLocus]
  rw [← piRight_lTensor_invDelta_apply k G M N x, ← piRight_lTensor_invConst_apply k G M N x]
  exact (TensorProduct.piRight k k N fun _ : G => M).injective.eq_iff.symm

/-- **The core lemma — invariants commute with `⊗` over a field.**
`N ⊗_k M^G ≃ₗ[k] (N ⊗_k M)^G`, where `G` is a finite group acting `k`-linearly on `M`, `N` an
arbitrary `k`-module (flat, since `k` is a field), and the action on `N ⊗ M` is through the
`M`-factor. Char-free: no averaging projector. -/
noncomputable def invariantsTensorEquiv :
    N ⊗[k] (invariantSubmodule k G M) ≃ₗ[k] tensorInvariantSubmodule k G M N := by
  haveI : Module.Free k N := Module.Free.of_divisionRing k N
  haveI : Module.Flat k N := Module.Flat.of_free
  refine LinearMap.tensorEqLocusEquiv k N (invDelta k G M) (invConst k G M) ≪≫ₗ
    LinearEquiv.ofEq _ _ ?_
  rw [← tensorInvariantSubmodule_eq k G M N]
  refine Submodule.ext fun x => ?_
  simp only [LinearMap.mem_eqLocus, TensorProduct.AlgebraTensorModule.coe_lTensor]

end Core

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
