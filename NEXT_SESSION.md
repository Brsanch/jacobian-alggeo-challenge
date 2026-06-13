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

### Next chip = **M1a-residual** (the equalizer identification)

M1a's def layer + cocycle lemma are DONE and merged (`55532a9`,
`Submission/CechModuleCat.lean`, CI-green). The remaining M1a piece:

**Identify the degree-0 Čech coboundary `d⁰` with the difference of the two
restriction maps**, turning `cechHZeroIsoKernel`'s `kernel (d⁰)` into the
literal **equalizer of the two restriction maps = global sections of the
cover**. Concretely, for `ι := Fin 2` (or a general 2-element index): exhibit
`((cechComplexMod U).obj P).d 0 1` (post-composed with the natural product
identifications of `Č⁰ ≅ P(U₀) ⊓ P(U₁)` and `Č¹`'s `U₀∩U₁` factor) as
`r₀ - r₁` where `r₀, r₁` are the two restriction maps `P(Uᵢ) ⟶ P(U₀∩U₁)`,
sorry-free. **DONE WHEN:** a lemma stating Čech `H⁰` is the equalizer
(`kernel (r₀ - r₁)`) of the two restriction maps, compiling at the pin.

- **The wall (state precisely if stuck):** `cechComplexFunctor` is brand-new
  (Joël Riou, 2026) with **zero downstream uses in mathlib** — no precedent
  for unfolding its differential. The differential is the
  `alternatingCofaceMapComplex` of the `cosimplicialObjectFunctor` (=`evalOp ⋙
  whiskeringLeft E.rightOp`) of `(FormalCoproduct.mk _ U).cech`. Degree-0
  object via `evalOp_obj_obj`: `∏ᶜ_{i : Fin 1 → ι} P.obj(op(∏ᶜ_{Fin 1} U∘i))`;
  the Fin-1 product/reindex collapse + the alternating-coface d⁰ are the two
  uncharted unfolds. The `@[simps!]` on `cosimplicialObjectFunctor`,
  `cochainComplexFunctor`, `evalOp`, `power`, `cech` are the levers.
- Gate: CI on a `loop/<ts>-m1a-equalizer` branch **until the local mathlib
  bootstrap finishes** (see "Local checks" below), then per-file
  `LEAN_NUM_THREADS=1 lake env lean Submission/CechModuleCat.lean`.

After M1a-residual: **M1b** (the curve's two-affine cover + restriction maps
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
