# Route — affine addition map `Sym^d × Sym^e → Sym^{d+e}`, brick (c): invariants-commute (2026-06-14)

The algebraic heart of the **group law (hole 3)**. Bricks (a) and (b) are DONE and merged-pending:
`tensorPowMulEquiv` (merge algebra-iso `A^{⊗d}⊗A^{⊗e} ≃ₐ A^{⊗(d+e)}`, `TensorPowerAdd.lean`) and
its `S_d×S_e ↪ S_{d+e}` equivariance (`TensorPowerAddEquivariant.lean`). Brick (c) is the remaining
substantive content, scoped here against a warm-cache mathlib survey (pin `5450b53e5ddc`).

## Target (the addition algebra hom)

On coordinate rings the divisor-concatenation map `Sym^d × Sym^e → Sym^{d+e}` dualizes to the
`k`-algebra hom
```
φ : (A^{⊗(d+e)})^{S_{d+e}}  →  (A^{⊗d})^{S_d} ⊗_k (A^{⊗e})^{S_e}
```
built as: `t ↦ (incl)⁻¹ ( tensorPowMulEquiv.symm t )`, where
`incl : (A^{⊗d})^{S_d} ⊗_k (A^{⊗e})^{S_e} ↪ A^{⊗d} ⊗_k A^{⊗e}` is the subalgebra-tensor inclusion.
Then `Spec φ` over `Spec k` is the addition map; the affine `AffineQuotient`/`affineSymmetricPower`
packaging gives the scheme morphism.

For `φ` to be defined we need two facts about `incl`:
- **(c-i) `incl` injective** — so `incl⁻¹` is defined on its range. ✅ **DONE 2026-06-14**
  (`Submission/Jacobian/TensorOverFieldInjective.lean`): `tensorMap_injective_of_field` (tensor of
  injective `k`-linear maps over a field is injective, via `TensorProduct.map_injective_of_flat_flat`
  + field ⟹ free ⟹ flat) and its corollary `subalgebra_tensorMap_val_injective`.
- **(c-ii) `tensorPowMulEquiv.symm t ∈ range incl`** for `t` an `S_{d+e}`-invariant — THE HARD,
  FIELD-DEPENDENT STEP. By brick (b) the image is `(S_d×S_e)`-invariant, i.e. lands in
  `(A^{⊗d} ⊗ A^{⊗e})^{S_d×S_e}`; and `range incl = (A^{⊗d})^{S_d} ⊗ (A^{⊗e})^{S_e}`. So (c-ii) ⟺
  **`(A^{⊗d} ⊗_k A^{⊗e})^{S_d×S_e} = (A^{⊗d})^{S_d} ⊗_k (A^{⊗e})^{S_e}`** — invariants commute with `⊗`
  over a field. This is the genuine mathlib gap.

## Why char-free (the obstruction the field handles, NOT the averaging projector)

The challenge curve is over an **arbitrary** field `k`, so `char k` may divide `d! = |S_d|`. mathlib's
Reynolds/averaging projector `Representation.averageMap` needs `[Invertible (Fintype.card G : k)]`
(`RepresentationTheory/Invariants.lean:122`) — **unavailable** here. The correct char-free route is
**flatness/exactness**: over a field every module is flat, and flat base change commutes with kernels
/ equalizers, hence with invariants.

## The core lemma and its CONFIRMED substrate

**Core:** for a field `k`, a finite group `G` acting `k`-linearly on `M`
(`[Finite G] [DistribMulAction G M] [SMulCommClass G k M]` — exactly the repo's `permAction` +
`SMulCommClass`), and any `k`-module `N` (flat, since `k` a field):
```
(N ⊗_k M)^G  ≅  N ⊗_k M^G      (G acting on N⊗M through the M-factor)
```
Assembly (all pieces verified present at the pin):
1. **Invariants as an equalizer.** `δ, c : M →ₗ[k] (G → M)` with `δ m = fun g => g • m`,
   `c m = fun _ => m`. Then `M^G = LinearMap.eqLocus δ c` (membership: `∀ g, g•m = m`). Likewise the
   `G`-action on `N⊗M` is `g • x = (lTensor N (toLinearMap g)) x`, and `(N⊗M)^G = eqLocus δ' c'`,
   `δ' x = fun g => g • x`.
2. **Flat base change commutes with the equalizer** — `LinearMap.tensorEqLocusEquiv`
   (`Mathlib/RingTheory/Flat/Equalizer.lean:165`, `[Module.Flat k N]`):
   `N ⊗ eqLocus(δ, c) ≃ₗ eqLocus(N⊗δ, N⊗c)`. (Underlying `Module.Flat.eqLocus_lTensor_eq`,
   `:41`.) So `N ⊗ M^G ≅ eqLocus(lTensor N δ, lTensor N c)`.
3. **Match `eqLocus(N⊗δ, N⊗c)` with `(N⊗M)^G`** via `TensorProduct.piRight`
   (`Mathlib/LinearAlgebra/TensorProduct/Pi.lean:96`): `N ⊗ (G → M) ≃ₗ (G → N⊗M)`, intertwining
   `lTensor N δ` with `δ'` and `lTensor N c` with `c'` (naturality: `piRight ∘ lTensor N δ = δ'`,
   a `piRight_tmul`/`Pi.single` computation — the fiddly step). Hence
   `eqLocus(N⊗δ, N⊗c) ≅ eqLocus(δ', c') = (N⊗M)^G`.
4. Compose 2+3: `N ⊗ M^G ≅ (N⊗M)^G`.

**Apply twice** for the two-group statement: `(M⊗N)^{S_d×S_e} = (M⊗N)^{S_d}` (only `S_d` acts, on `M`)
`∩ {H-inv}` … cleaner: `(M⊗N)^{S_d×S_e} = ((M⊗N)^{S_d})^{S_e} = (M^{S_d} ⊗ N)^{S_e} = M^{S_d} ⊗ N^{S_e}`,
using core with `G=S_d` on the `M`-factor, then `G=S_e` on the `N`-factor (symmetric form of core).

## Field ⟹ flat (the instance to supply locally, as in (c-i))

No global `[Field k] → Module.Flat k V` instance at the pin. Supply:
`haveI : Module.Free k V := Module.Free.of_divisionRing k V; haveI : Module.Flat k V := .of_free`.
(Used and verified in `TensorOverFieldInjective.lean`.)

## Named obligations remaining (brick (c-ii) + assembly)

1. `M^G = eqLocus δ c` (submodule equality; the `δ/c` `LinearMap`s + `SMulCommClass` linearity).
2. The `G`-action on `N⊗M` as a `DistribMulAction` (instance from `lTensor N (toLinearMap g)`).
3. `piRight` naturality `piRight ∘ lTensor N δ = δ'` (and for `c`) — the one genuinely fiddly step.
4. Core `(N⊗M)^G ≅ N ⊗ M^G` (compose `tensorEqLocusEquiv` + `piRight`).
5. Two-group `(M⊗N)^{S_d×S_e} = M^{S_d} ⊗ N^{S_e}` (apply core twice; the symmetric/`M`-factor form).
6. Bridge to the repo's `FixedPoints.subalgebra k (TensorPow R A d) (Perm (Fin d))` (its underlying
   submodule = `M^{S_d}`) and the diagonal `S_d×S_e` action on `A^{⊗d}⊗A^{⊗e}`.
7. Assemble `φ` (corestrict `tensorPowMulEquiv.symm` along (c-i)+(5)) and `Spec φ` = the addition map;
   wire to `affineSymmetricPower` / `AffineQuotient`.

Obligations 1–4 are the core lemma; 5–7 are assembly on top of present theorems. None require new
mathlib *theory* — the flat-equalizer engine (`tensorEqLocusEquiv`) and `piRight` are present; this is
careful assembly, multi-session in volume but not a non-interpolative leap.

## Sources
- mathlib: `RingTheory/Flat/Equalizer.lean` (`tensorEqLocusEquiv`, `eqLocus_lTensor_eq`),
  `RingTheory/Flat/Basic.lean` (`map_injective_of_flat_flat`, `*_preserves_injective_linearMap`),
  `LinearAlgebra/TensorProduct/Pi.lean` (`piRight`), `RepresentationTheory/Invariants.lean`
  (why `averageMap` is unavailable).
- This is the affine-side group-law content; the birational group-law extension then needs RR
  (Tower A / Stack II).
