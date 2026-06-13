# NEXT SESSION — entry protocol

Read in order: `OPEN.md` (authoritative hole status) → `CHIP_GATES.md` →
`DEVELOPMENT.md` → `docs/ROUTE_RESEARCH_2026_06_13.md`. Do not re-audit; the
next chip is named below.

## Current phase: M1b (M0 + M1a-abstract done)

**M1a abstract layer COMPLETE** (loop runs #2–#4): `cechComplexMod`, `cechH`,
`cechHZeroIsoKernel`, `cechCosimpl`, `cechComplexMod_d_zero_one` (`d⁰=δ⁰−δ¹`),
and now `cechHZeroIsoEqualizer` (`H⁰ ≅ equalizer(δ⁰,δ¹)` — the degree-0
Čech/sheaf condition) are all merged + CI-green (`92a91be`, run `27454972985`).
The remaining coface coordinate-unfold is folded into M1b (see sub-task B below).

## (archive) M1 decomposition + encoding fork

**M0:** DONE — scaffold + CI green + `lake-manifest.json` committed
(commit `3a3066d`). M0 CI runs are green in 3–4 min, so the **CI-side
mathlib cache is warm** and a branch CI run is a fast, reliable gate.

**M1 pre-work done (loop run #1, 2026-06-13):** the declaration-level mathlib
API inventory + the k-module encoding decision are now recorded in
`docs/ROUTE_RESEARCH_2026_06_13.md` ("M1 API actuals + encoding decision").
Headline: define `H¹ C 𝒪_C` as the degree-1 homology of the two-affine-cover
Čech complex **in `ModuleCat k`** (`cechComplexFunctor`, which is preadditive-
`A`-generic) — the abelian-group `Sheaf.H` cannot carry the k-module
structure the DONE WHEN needs. M1 is split into M1a/M1b/M1c (see route doc).

### Next chip = **M1b** (the curve's concrete two-affine cover + restriction maps)

M1a's abstract layer is closed (see top of file). M1b makes the cover and
presheaf concrete and is the gateway to M1c (Serre finiteness = go/no-go).
Pick ONE sub-chip per run (DONE WHEN each):

- **B-cover:** instantiate the abstract `cechH`/`cechHZeroIsoEqualizer` at the
  curve `C`'s **two-affine cover** `U : Fin 2 → (the scheme's open/affine
  category)` with `𝒪_C` as a `ModuleCat k`-valued presheaf. **DONE WHEN:** a
  `def` producing the genus-relevant `cechH U 1` (resp. `cechHZeroIsoEqualizer`)
  specialized to `(C, 𝒪_C, U)`, compiling at the pin. (First survey what
  AlgebraicGeometry API in the pin gives an affine cover + the structure-sheaf
  sections as `k`-modules — mathlib-first, per Gate 6.)
- **B-coface (coordinate-unfold, optional refinement):** identify the abstract
  cofaces `(cechCosimpl U P).δ 0`, `.δ 1` *concretely* as the `Pi.lift`-of-
  `P.map` restriction maps onto pairwise intersections, so the equalizer of
  `cechHZeroIsoEqualizer` reads literally as the equalizer of the two
  restriction maps `∏ᵢ P(Uᵢ) ⇉ ∏_{i,j} P(Uᵢ∩Uⱼ)`. **DONE WHEN:** a lemma giving
  `(cechCosimpl U P).δ a` componentwise (`≫ Pi.π _ j`) as `Pi.π _ (j∘δa) ≫ P.map …`.
  Lower priority than B-cover (it is bookkeeping; the equalizer statement already
  holds abstractly). Full recipe preserved below.

#### Coface coordinate-unfold recipe (worked out loop run #3 from the verbatim pinned sources)

`X := cechCosimpl U P`. `X.δ a = X.map (SimplexCategory.δ a)` unfolds as (all
`@[simps!]`/`@[simps]`, so simp lemmas exist):
- `X = (evalOp P) ⋙ E.rightOp`, `E := (mk _ U).cech`; so
  `X.obj ⦋n⦌ = (evalOp.obj P).obj (op (E.obj ⦋n⦌))`.
- `evalOp.obj P` (`FC/Basic.lean:383`, `@[simps!]`):
  `.obj V = ∏ᶜ_{i : V.unop.I} P.obj(op(V.unop.obj i))`,
  `.map f = Pi.lift fun i ↦ Pi.π _ (f.unop.f i) ≫ P.map (f.unop.φ i).op`.
- `E.obj ⦋n⦌ = (mk U).power (Fin (n+1))` (`FC/Cech.lean:186`, `@[simps]`):
  `.I = Fin(n+1) → ι`, `.obj i = ∏ᶜ (U ∘ i)` (`power`, `FC/Cech.lean:34`).
- `E.map g = (mk U).mapPower g.unop.toOrderHom.toFun`; `mapPower`
  (`FC/Cech.lean:122`, `@[simps -fullyApplied]`): `.f i = i ∘ f`,
  `.φ _ = Pi.lift (fun _ ↦ Pi.π _ _)`. `E.rightOp.map (δ a) = (E.map (δ a).op).op`.

For `a : Fin 2` (the two cofaces of `δ⁰`): `δ a : ⦋0⦌ ⟶ ⦋1⦌` is the order-hom
`Fin 1 ↪ Fin 2` skipping `a`. So `X.δ a : X⁰ = ∏_{i:Fin 1→ι} P(∏ᶜ U∘i) ⟶
X¹ = ∏_{j:Fin 2→ι} P(∏ᶜ U∘j)` is, via `evalOp.map`'s `Pi.lift`/`Pi.π`, the map
whose `j`-component projects onto the `(j ∘ δa)`-factor of `X⁰` then applies `P`
of the `mapPower`-`Pi.lift` inclusion `∏ᶜ U∘(j∘δa) ⟶ ∏ᶜ U∘j` (= restriction
`P(U_{j∘δa}) ⟶ P(U_j)`). For `ι = Fin 2`: the four `j : Fin 2 → Fin 2` factors
split into the diagonal (`j` const → both cofaces agree → cancels in `δ⁰−δ¹`)
and the off-diagonal `U₀∩U₁` factors where `δ⁰` keeps index-1 and `δ¹` keeps
index-0 → `r₁ − r₀` on the `U₀∩U₁` factor. So `kernel(δ⁰−δ¹) ≅ equalizer(r₀,r₁)`.

- **Levers:** the `@[simps!]` of `cosimplicialObjectFunctor`, `evalOp`,
  `power`, `mapPower`, `cech`, plus `Pi.lift_π`, `limit.lift_π`,
  `Fin.sum_univ_two`. Expect a much larger chip than the first unfold (4-factor
  `X¹` reindex bookkeeping) — consider splitting (state `X.δ a` componentwise
  first, then assemble the equalizer).
- **Tactic notes from the first unfold (reuse):** switching the complex object
  inside `.d` breaks the motive (dependent type) — use `show`/defeq not `rw`;
  `CochainComplex.of_d` needs `erw` (`1` vs `0+1`); finish sign algebra with
  `abel`.
- Gate: CI on a `loop/<ts>-m1a-equalizer` branch **until the local mathlib
  bootstrap finishes** (see "Local checks" below), then per-file
  `LEAN_NUM_THREADS=1 lake env lean Submission/CechModuleCat.lean`.

After M1b: **M1c** (`FiniteDimensional k ((cechH U 1).obj 𝒪_C)` = Serre
finiteness = the go/no-go datum). Record M1's actual LOC + wall-clock in the
route doc when M1c lands; make the go/no-go call explicitly in `LOOP_LOG.md`.

### Local checks (loop run #2 correction)

The "bootstrap running v4.29.0" flag in run #1 was a **misattribution**: pid
59568 is the **ns-lean-proofs** repo's bootstrap (v4.29.0), not alggeo's.
alggeo's mathlib was never checked out (only `.git`) → its local bootstrap had
not started, so this run gated on CI (correct per protocol). Run #2 launched a
**chained background bootstrap**: it waits for the ns-lean-proofs build to
finish (no concurrent `lake build` — apfsd panic rule), then runs the throttled
`taskpolicy -b nice -n 19 … lake build` in alggeo (logs to `bootstrap.log`,
gitignored). Once it completes, future runs get warm-cache per-file
`lake env lean` (jacobian's oleans can't be borrowed: rc1 vs our rc2, different
mathlib rev). If `bootstrap.log` shows it finished green, prefer local
iteration over CI.

## Arc DONE WHEN

A submission accepted by the lean-eval comparator for
`jacobian_challenge_alggeo` (all 9 holes, sorry-free, axiom-free) and
audited by the maintainer.
