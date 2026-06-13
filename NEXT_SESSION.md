# NEXT SESSION — entry protocol

Read in order: `OPEN.md` (authoritative hole status) → `CHIP_GATES.md` →
`DEVELOPMENT.md` → `docs/ROUTE_RESEARCH_2026_06_13.md`. Do not re-audit; the
next chip is named below.

## Current phase: M1 (M0 done; M1 decomposed + encoding fork resolved)

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

### Next chip = **M1a-equalizer** (the SECOND differential-unfold)

M1a's def layer, cocycle lemma, AND the **first** differential-unfold
(`d⁰ = δ⁰ − δ¹`, `cechComplexMod_d_zero_one`) are DONE and merged
(`55532a9`, `681626a`, `Submission/CechModuleCat.lean`, CI-green). The
remaining M1a piece — the second, harder unfold:

**Identify the two cofaces `(cechCosimpl U P).δ 0`, `.δ 1` concretely as the
restriction maps onto pairwise intersections**, turning `kernel (δ⁰ − δ¹)`
into the literal **equalizer of the two restriction maps = global sections of
the cover**. **DONE WHEN:** a lemma stating Čech `H⁰` is the equalizer
(`kernel (r₀ − r₁)`) of the two restriction maps, compiling at the pin.

#### Full recipe (worked out loop run #3 from the verbatim pinned sources)

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

After M1a-equalizer: **M1b** (the curve's two-affine cover + restriction maps
from the scheme's instances; wire in `𝒪_C` as a `ModuleCat k`-presheaf), then
**M1c** (`FiniteDimensional k (cechH U 1 .obj 𝒪_C)` = Serre finiteness = the
go/no-go datum). Record M1's actual LOC + wall-clock in the route doc when M1c
lands; make the go/no-go call explicitly in `LOOP_LOG.md`.

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
