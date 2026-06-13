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

### Next chip = **M1a** (write code)

Define the two-object Čech complex of `𝒪_C` in `ModuleCat k` via
`cechComplexFunctor` on a `Fin 2`-indexed affine cover, and define
`H1 C 𝒪_C := (that complex).homology 1`. **Substantive lemma it must also
prove (gate 5/7):** Čech `H⁰` = equalizer of the two restriction maps
(global sections of the cover), sorry-free. **DONE WHEN:** `H1 C 𝒪_C :
ModuleCat k` + the H⁰/equalizer lemma compile sorry-free at the pin.
- Before writing: **gate-6 check** on the now-warm local tree — grep
  `cechComplexFunctor` / `Cech` usages for an existing `H⁰ ≅ Γ` or
  equalizer lemma; if one exists within ~50 LOC of glue, consume it rather
  than re-prove. Also `elan show` / check the bootstrap actually built
  `v4.30.0-rc2` oleans (run #1 saw the bootstrap running **v4.29.0** — a
  mismatch; if oleans are 4.29.0 they're unusable, re-launch the build).
- Gate via CI on a `loop/<ts>-m1a-cech-modulecat` branch (cache cold locally
  until the bootstrap finishes under the correct toolchain).

After M1a: **M1b** (the curve's two-affine cover + restriction/intersection
maps exist), then **M1c** (`FiniteDimensional k (H1 C 𝒪_C)` = Serre
finiteness = the go/no-go datum). Record M1's actual LOC + wall-clock in the
route doc when M1c lands, and make the go/no-go call explicitly in
`LOOP_LOG.md`.

## Arc DONE WHEN

A submission accepted by the lean-eval comparator for
`jacobian_challenge_alggeo` (all 9 holes, sorry-free, axiom-free) and
audited by the maintainer.
