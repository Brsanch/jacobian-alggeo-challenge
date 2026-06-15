import Mathlib

/-!
# Intersection of tensor subspaces over a field

For subspaces `p ⊆ M`, `q ⊆ N` of `k`-vector spaces, the two "slab" subspaces
`p ⊗ N` and `M ⊗ q` of `M ⊗ N` meet exactly in `p ⊗ q`:
```
(p ⊗ N) ⊓ (M ⊗ q)  =  p ⊗ q          (inside M ⊗ N)
```
where the subspaces are the ranges of `p.subtype.rTensor N`, `q.subtype.lTensor M`, and
`TensorProduct.map p.subtype q.subtype` respectively (equivalently `Submodule.map₂ (mk k M N) p ⊤`
etc. via `TensorProduct.range_mapIncl`).

This is the **flatness gap** behind the affine addition map `Sym^d × Sym^e → Sym^{d+e}` (group law,
hole 3): it lets the two-group invariants statement
`(A^{⊗d} ⊗ A^{⊗e})^{S_d×S_e} = (A^{⊗d})^{S_d} ⊗ (A^{⊗e})^{S_e}` be assembled WITHOUT any
equivariance transport — the product-group fixed points are the intersection of the two factor-wise
fixed-point slabs (each `= p ⊗ N` / `M ⊗ q` by the single-group core lemma), and this lemma collapses
that intersection to `p ⊗ q = range(incl)`.

The proof is the standard flat-exactness argument: `(p ⊗ N)` is `ker(p.mkQ ⊗ id_N)` (right-exactness
of `· ⊗ N` on `0 → p → M → M⧸p → 0`); an element of the intersection, written `(id_M ⊗ q.subtype) y`,
is killed by `p.mkQ ⊗ id_N`, which factors as `(id_{M⧸p} ⊗ q.subtype) ∘ (p.mkQ ⊗ id_q)`; the first
factor is injective (`M⧸p` flat over a field), so `(p.mkQ ⊗ id_q) y = 0`, i.e. `y ∈ p ⊗ q`, whence
the original element lies in `p ⊗ q`. Route-independent, mathlib-PR-shaped.
-/

set_option maxHeartbeats 1000000

open scoped TensorProduct
open LinearMap

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

/-- **Intersection of tensor subspaces over a field.** Inside `M ⊗_k N`,
`(p ⊗ N) ⊓ (M ⊗ q) = p ⊗ q`. -/
theorem tensorSubspace_inf {k : Type u} [Field k]
    {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (p : Submodule k M) (q : Submodule k N) :
    LinearMap.range (p.subtype.rTensor N) ⊓ LinearMap.range (q.subtype.lTensor M)
      = LinearMap.range (TensorProduct.map p.subtype q.subtype) := by
  haveI : Module.Free k (M ⧸ p) := Module.Free.of_divisionRing k (M ⧸ p)
  haveI : Module.Flat k (M ⧸ p) := Module.Flat.of_free
  apply le_antisymm
  · -- the substantive direction
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxpN, hxMq⟩ := hx
    -- `p ⊗ N = ker(p.mkQ ⊗ id_N)` by right-exactness, so `x` is killed by `p.mkQ ⊗ id_N`.
    have hexact : Function.Exact (p.subtype.rTensor N) (p.mkQ.rTensor N) :=
      _root_.rTensor_exact N (LinearMap.exact_subtype_mkQ p) (Submodule.mkQ_surjective p)
    have hx0 : p.mkQ.rTensor N x = 0 := by
      have hmem : x ∈ LinearMap.ker (p.mkQ.rTensor N) := by
        rw [LinearMap.exact_iff.mp hexact]; exact hxpN
      exact hmem
    -- write `x = (id_M ⊗ q.subtype) y`
    obtain ⟨y, rfl⟩ := hxMq
    -- `(p.mkQ ⊗ id_N) ∘ (id_M ⊗ q.subtype) = (id ⊗ q.subtype) ∘ (p.mkQ ⊗ id_q)`
    rw [← LinearMap.comp_apply, rTensor_comp_lTensor, ← lTensor_comp_rTensor,
      LinearMap.comp_apply] at hx0
    -- `id_{M⧸p} ⊗ q.subtype` is injective (`M⧸p` flat), so `(p.mkQ ⊗ id_q) y = 0`
    have hinj : Function.Injective (q.subtype.lTensor (M ⧸ p)) :=
      Module.Flat.lTensor_preserves_injective_linearMap q.subtype q.injective_subtype
    have hy0 : p.mkQ.rTensor (↥q) y = 0 := by
      apply hinj; rw [hx0, map_zero]
    -- so `y ∈ ker(p.mkQ ⊗ id_q) = range(p.subtype ⊗ id_q) = p ⊗ q`
    have hexact2 : Function.Exact (p.subtype.rTensor (↥q)) (p.mkQ.rTensor (↥q)) :=
      _root_.rTensor_exact (↥q) (LinearMap.exact_subtype_mkQ p) (Submodule.mkQ_surjective p)
    have hy_range : y ∈ LinearMap.range (p.subtype.rTensor (↥q)) := by
      rw [← LinearMap.exact_iff.mp hexact2, LinearMap.mem_ker]; exact hy0
    obtain ⟨z, rfl⟩ := hy_range
    -- and `(id_M ⊗ q.subtype) ∘ (p.subtype ⊗ id_q) = p.subtype ⊗ q.subtype`
    exact ⟨z, by rw [← lTensor_comp_rTensor, LinearMap.comp_apply]⟩
  · -- `p ⊗ q ≤ p ⊗ N` and `≤ M ⊗ q`
    apply le_inf
    · rw [← rTensor_comp_lTensor]
      exact LinearMap.range_comp_le_range _ _
    · rw [← lTensor_comp_rTensor]
      exact LinearMap.range_comp_le_range _ _

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
