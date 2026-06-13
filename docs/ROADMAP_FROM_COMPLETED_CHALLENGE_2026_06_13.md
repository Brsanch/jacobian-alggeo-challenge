# Top-down roadmap from the COMPLETED Riemann-surface Jacobian challenge (2026-06-13)

Kevin Buzzard's Jacobian challenge (compact Riemann surfaces) was solved end-to-end by
**rkirov/jacobian-claude** (2026-06-11). This doc uses that completed solution's *structure*
as a top-down roadmap for Merten's **alggeo** analogue (this repo), and — crucially — marks
the exact point where the analytic roadmap stops transferring to the scheme category.

Source for the skeleton: `jacobian-lean-challenge/JacobianChallenge/Basic.lean` (the 24-item
API). Note: the two challenges are in **disjoint mathlib categories** (complex manifolds vs
schemes); 0/480 Buzzard files touch the `Scheme`/`SheafOfModules` API. So this is a roadmap of
*structure and proof-strategy*, never of Lean code.

## The completed solution's spine (Riemann surface)

`genus X := dim_ℂ H⁰(X, Ω¹)`  →  `Jacobian X := ℂ^{genus}/Λ` (period lattice Λ)  →  equipped
with `[AddCommGroup]` `[CompactSpace]` `[ChartedSpace (ℂ^g)]` `[IsManifold]` `[LieAddGroup]`
(= a complex torus = the abelian variety)  →  `ofCurve P : X → Jacobian X` (Abel–Jacobi,
`p ↦ ∫_P^p ω`)  →  `pushforward`/`pullback`/`ContMDiff.degree` (functoriality).

## Hole-by-hole map (alggeo ← completed Riemann-surface analogue)

| alggeo hole | RS analogue (completed) | scheme realisation | foundation needed | roadmap transfer |
|---|---|---|---|---|
| **1 `genus`** | `dim_ℂ H⁰(Ω¹)` | `dim_k H¹(C,𝒪)` (Serre-dual) | **Serre finiteness** (Stack II.1) | **STRUCTURE ✓** — same number, dual def. Both gate on coherent-cohomology finiteness. RS got it free (Hodge/`ℂᵍ`); alggeo must build Serre finiteness. |
| **2 `Jacobian`** | `ℂᵍ/Λ` (analytic uniformization) | `Pic⁰ C` (FGA) **or** `Sym^g C` birational | **the entire construction** (Stack I + Pic⁰ representability / Sym^d) | **DIVERGES — roadmap silent.** RS uses the analytic torus, which has NO algebraic analogue over general `k`. This is where the completed solution was *easy* and alggeo is *hardest*. |
| **3 `instGrpObj`** | `AddCommGroup (ℂᵍ/Λ)` (free from quotient) | `GrpObj (Pic⁰)` / birational group law | group structure on the construction | **STRATEGY** — RS gets it free from the quotient; alggeo needs the algebraic group law (birational-group-law thm / Pic functor group). Confirms hole-3 is *downstream of hole 2*. |
| **4 `smoothOfRelativeDimension (genus)`** | `ChartedSpace (ℂᵍ)` + `IsManifold` (dim g) | `SmoothOfRelativeDimension g` | smoothness of the construction; `dim = g` | **STRUCTURE ✓** — confirms "Jacobian is smooth of dim = genus". Tower C built `smooth_of_grpObj` (the smoothness *engine*); the `dim = g` ties to hole 1. RS: dim from the chart `ℂᵍ`. |
| **5 `instIsProper`** | `CompactSpace (ℂᵍ/Λ)` | `IsProper (Pic⁰).hom` | properness of the construction | **STRUCTURE ✓** — proper ↔ compact. RS: compact from `ℝ^{2g}/ℤ^{2g}`. alggeo: properness of Pic⁰ / `Sym^g`. |
| **6 `instGeometricallyIrreducible`** | `ConnectedSpace (ℂᵍ/Λ)` | `GeometricallyIrreducible` | irreducibility of the construction | **STRUCTURE ✓** — connected ↔ geom-irreducible. RS: torus connected. |
| **7 `ofCurve`** | `ofCurve P : p ↦ ∫_P^p ω` | `C → Pic⁰`, `p ↦ 𝒪(p−P)` | Abel–Jacobi as a scheme morphism | **STRATEGY** — same *role* (curve → its Jacobian, base-pointed at `P`), totally different realisation (integration vs degree-0 divisor class). |
| **8 `comp_ofCurve`** | `ofCurve P P = 0` (basepoint ↦ 0) | `P ≫ ofCurve P = η` | the basepoint normalisation | **STRATEGY ✓** — same identity; trivial once 7 exists. |
| **9 `exists_unique_ofCurve_comp`** (Albanese univ. prop.) | **not a Buzzard hole** | `∃! g, f = ofCurve P ≫ g` | rigidity + generation (curve generates Jacobian) | **NO roadmap** — alggeo-specific (Buzzard's API has functoriality/degree instead of the Albanese universal property). Tower C already built the **uniqueness half** + rigidity; the *existence* half (factor any pointed map) is new. |

## What the roadmap tells us (decisions)

1. **The hole structure is confirmed and standard.** Holes 3–6 are exactly "the Jacobian is an
   abelian variety" (group + proper + smooth-of-dim-g + irreducible), holes 1/7/8 are
   genus / Abel–Jacobi / basepoint, hole 9 is the Albanese. The completed solution validates
   that this is the right decomposition and that **holes 3,4,5,6 are all downstream of hole 2**
   (the construction): you get them *from* the constructed object.

2. **The roadmap is silent exactly at the alggeo's hard core (hole 2).** The completed challenge
   is "end-to-end" largely *because* the Riemann-surface Jacobian has the analytic `ℂᵍ/Λ`
   construction (compact, group, manifold all fall out of the quotient). Over an arbitrary field
   there is no such shortcut — hole 2 must be `Pic⁰` (FGA representability) or `Sym^g` birational,
   i.e. the multi-month Stack-I + construction work. **So the completed solution helps with the
   *frame* (holes 1,3–8 structure) but not the *bulk* (hole 2 + its Stack-I foundation).**

3. **Serre finiteness (Stack II.1) is confirmed load-bearing for hole 1** either way (RS got the
   genus from Hodge theory on `ℂ`; alggeo needs `FiniteDimensional k H¹`).

4. **Hole 9 has no roadmap** — but Tower C already built its uniqueness half + Mumford rigidity;
   the existence half (the curve generates the Jacobian ⇒ any pointed map factors) is the new piece.

## Build order implied (top-down ∩ the bottom-up foundation stacks)

The roadmap + `SHARED_FOUNDATION_ROUTE_2026_06_13.md` agree on the critical path:
**Stack I (sheaves of modules → Pic) and Stack II (cohomology → Serre finiteness) → hole 2
(`Jacobian = Pic⁰`, the bulk) → holes 3,5,6 fall out of the construction (Tower C's
abelian-variety theory wires in) → hole 1 (`genus = dim H¹`, needs II.1) + hole 4 (`dim = g`)
→ holes 7,8 (Abel–Jacobi) → hole 9 (Albanese existence; Tower C has uniqueness).**

Net: the completed challenge is a strong confirmation of the *target shape* and the *downstream
ordering*, and a precise reminder that the alggeo's hardest, bulkiest piece — the algebraic
construction of `Pic⁰` — is exactly the part the analytic solution got for free and therefore
cannot guide. The foundation work (Stacks I & II) remains the gate.
