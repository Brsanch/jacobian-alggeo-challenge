# Open items — jacobian-alggeo-challenge

> **Before any new Lean work: read `CHIP_GATES.md` (repo root)** — vacuity
> lint gate (mechanical, baseline-ratcheted) + the anti-paraphrase gates —
> and `DEVELOPMENT.md` (panic-safe build rules, eval submission mechanics).

## Authoritative current state (2026-06-13: scaffold, all 9 holes OPEN)

Target: the official lean-eval problem
[`jacobian_challenge_alggeo`](https://lean-lang.org/eval/problems/jacobian_challenge_alggeo/)
(Christian Merten's algebraic-geometry analogue of the Buzzard Jacobian
challenge; the diffgeo variant was solved by rkirov/jacobian-claude
2026-06-11). DONE WHEN (arc): a submission accepted by the lean-eval
comparator and audited by the maintainer. Status board: Kim Morrison's
[Manifold market](https://manifold.markets/kimem/when-will-the-jacobian-challenge-be).

| # | Hole | Kind | Status |
|---|------|------|--------|
| 1 | `genus` | def | OPEN |
| 2 | `Jacobian` | def | OPEN |
| 3 | `Jacobian.instGrpObj` | def | OPEN |
| 4 | `Jacobian.smoothOfRelativeDimension_genus` | theorem | OPEN |
| 5 | `Jacobian.instIsProper` | theorem | OPEN |
| 6 | `Jacobian.instGeometricallyIrreducible` | theorem | OPEN |
| 7 | `Jacobian.ofCurve` | def | OPEN |
| 8 | `Jacobian.comp_ofCurve` | theorem | OPEN |
| 9 | `Jacobian.exists_unique_ofCurve_comp` | theorem | OPEN |

Current phase: **M1 (coherent cohomology canary)** — M0 done (scaffold + CI
green + manifest, `3a3066d`). See `docs/ROUTE_RESEARCH_2026_06_13.md`.

M1 declaration-level mathlib inventory + k-module **encoding decision** done
in loop run #1 (2026-06-13): `H¹ C 𝒪_C` will be the degree-1 homology of the
two-affine-cover Čech complex **in `ModuleCat k`** (`cechComplexFunctor` is
preadditive-generic; the abelian-group `Sheaf.H` can't carry the needed
k-module structure). M1 split into:

| M1 sub | content | status |
|---|---|---|
| M1a | abstract Čech complex in `ModuleCat k` + `cechH` def + H⁰≅ker(d⁰) | **PARTIAL** (`55532a9`) — def layer + cocycle lemma done; equalizer-as-restriction-difference is the residual |
| M1b | the curve's two-affine cover + restriction/intersection maps | OPEN |
| M1c | `FiniteDimensional k (H1 C 𝒪_C)` (Serre finiteness; go/no-go datum) | OPEN |

**M1a progress (loop run #2, 2026-06-13, `Submission/CechModuleCat.lean`, CI-green, merged `55532a9`):**
- `cechComplexMod (U : ι → C) : (Cᵒᵖ ⥤ ModuleCat k) ⥤ CochainComplex (ModuleCat k) ℕ` — `cechComplexFunctor` specialized to the preadditive target `ModuleCat.{w} k` with `ι : Type w`. **This compiles → the route-doc encoding decision is sound** (universe/instance resolution works at `A := ModuleCat.{w} k`, `ι : Type w`).
- `cechH (U) (n) : (Cᵒᵖ ⥤ ModuleCat k) ⥤ ModuleCat k` := `cechComplexMod U ⋙ homologyFunctor _ _ n`. So `FiniteDimensional k _` (M1c) is type-correct on `(cechH U n).obj P`.
- `cechHZeroIsoKernel : (cechH U 0).obj P ≅ kernel ((cechComplexMod U).obj P).d 0 1` — Čech H⁰ ≅ kernel of the first Čech coboundary (cocycle description; via `CochainComplex.isoHomologyπ₀` + `cyclesIsKernel`).
- **Residual (next M1a chip):** identify `d⁰` explicitly with the *difference of the two restriction maps* so the kernel becomes the literal *equalizer of the restriction maps / global sections of the cover*. This needs unfolding the brand-new (zero-downstream-use) `cechComplexFunctor` differential = `alternatingCofaceMapComplex` of the `evalOp`-evaluated `FormalCoproduct.cech` cosimplicial object. Abstract `ι`; the geometric `𝒪_C` + concrete 2-cover are M1b.

⚠️ Env flag (run #1): the local bootstrap `lake build` was running lean
**v4.29.0** while the pin is **v4.30.0-rc2** — verify the toolchain before
trusting local oleans (route doc "Environment flags"). CI (warm, ~3–4 min)
is the working gate meanwhile.

## Rules inherited from the diffgeo challenge post-mortems

- A "named hypothesis" introduced without a same-session discharge on
  arbitrary data is a renamed sorry (paraphrase gate, `CHIP_GATES.md`).
- Single bar: a hole counts CLOSED only when the declaration compiles
  sorry-free/axiom-free against the pinned mathlib AND its statement is
  byte-compatible with `Challenge.lean` (the comparator is the judge —
  do not invent softer tiers).
- Per-item status lives HERE, refreshed every session; prose docs and
  docstrings are not trustworthy for open/closed status.
