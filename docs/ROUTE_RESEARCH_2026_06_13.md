# Route research — alggeo Jacobian challenge (2026-06-13)

Per the route-research-before-arc rule: candidate textbook routes BEFORE any
construction work, with the mathlib-support inventory they sit on. Citations
are section-level; **exact theorem/page numbers are TO-VERIFY on first read
of each source — never cite them from memory in a proof comment.**

## What the 9 holes actually force

- `genus` is not free-floating: hole 4 (`SmoothOfRelativeDimension (genus C)
  (Jacobian C).hom`) forces the honest `g`. The identity component of the
  Picard scheme has tangent space `T₀ J ≅ H¹(C, 𝒪_C)` (deformation theory),
  so any workable `genus` definition must be provably equal to
  `dim_k H¹(C, 𝒪_C)` — there is no cohomology-free dodge.
- Hole 9 (Albanese universal property) is, per the problem's own metadata,
  "the no-cheating clamp": it quantifies over ALL abelian varieties `A`
  (smooth + proper + `GrpObj` + geometrically irreducible), so `Jacobian`
  cannot be a degenerate placeholder.
- The comparator pins every statement; helpers must be inlined in the
  submission workspace (no external deps beyond the pinned mathlib).

## Mathlib support at the pin (`5450b53e5ddc`, inventoried 2026-06-13, 9065 modules)

**Present** (vocabulary layer — much of it Merten's):
`Over`-category + `GrpObj` group objects incl.
`AlgebraicGeometry/Group/{Smooth,Abelian}`; morphism properties `IsProper`,
`SmoothOfRelativeDimension`, `GeometricallyIrreducible` (+ the
`Geometrically/` family); `ProjectiveSpectrum` (incl. `Proper.lean`);
`AlgebraicGeometry/FunctionField.lean`; `Cover/*`, `Gluing*`,
`Morphisms/Descent`; abstract sites-level sheaf cohomology
(`CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}`).
140 paths under `AlgebraicGeometry/`.

**Absent** (construction layer — ALL of it is on us):
Picard functor/scheme; divisors on schemes/curves; Riemann–Roch; coherent
cohomology of schemes (finiteness, base change); Hilbert/Quot schemes;
symmetric powers of schemes; quotients by finite group actions; abelian-
variety theory (rigidity etc.); Albanese.

## Candidate routes

### Route A — Weil's construction via symmetric powers (classical)

Sources: Milne, *Jacobian Varieties* (in Cornell–Silverman eds., *Arithmetic
Geometry*, Springer 1986; free at jmilne.org/math/articles) — construction
§§2–7: symmetric powers `C^(d)` are smooth projective; for `d = g` the
Abel–Jacobi map `C^(g) → Pic^g` is birational; birational group law via
Riemann–Roch; extend to a group variety by the theorem on birational group
laws (also BLR, *Néron Models*, ch. 5). Serre, *Groupes algébriques et
corps de classes*, ch. V for the divisor/AJ formalism.

Needs: finite-group quotients of quasi-projective schemes (for `Sym^d C`),
curve Riemann–Roch, function-field/birational machinery, the group-law
extension theorem. Everything is 1-variable classical; no Hilbert schemes.

### Route B — FGA representability of Pic⁰ (the "real thing")

Sources: Kleiman, *The Picard Scheme* (FGA Explained, AMS Surveys 123,
2005, ch. 9) — representability for projective geometrically integral
schemes over a field; smoothness + dimension of `Pic⁰` for curves via
deformation theory. Prerequisites: Hilbert/Quot (FGA Explained ch. 5–7),
flattening stratification, cohomology-and-base-change (Mumford, *Abelian
Varieties* §5; Hartshorne III.12).

Needs: the deepest infrastructure stack, but the trunk is maximally
mathlib-PR-able and reusable. Strictly larger than Route A for this
challenge alone.

### Route C — hybrid (A's construction, functorial packaging)

Build via symmetric powers (A) but state `Pic⁰` functorially so hole 9
(Albanese) follows from functoriality + rigidity of abelian varieties
(Mumford AV §4: pointed maps of abelian varieties are homomorphisms;
factorization through AJ: Milne JV §6) instead of ad-hoc birational
arguments. Likely the target shape regardless of A-vs-B.

## Shared prerequisite = the calibration canary

**M1: coherent cohomology for curves.** `H⁰/H¹` of coherent sheaves on a
proper curve, finite-dimensional over `k`, computable by Čech on a
two-affine cover (a smooth projective curve minus a closed point is affine —
classical; verify the geometrically-irreducible-over-arbitrary-`k` form).
Every route consumes M1 (genus, RR, tangent space, smoothness-of-dim-g),
and it is the single best-calibrated probe of cost-per-classical-theorem in
mathlib's current AG idiom.

## Milestones (each gets a DONE WHEN before work starts)

| ID | Content | DONE WHEN |
|----|---------|-----------|
| M0 | Scaffold + CI + manifest | CI green on scaffold; `lake-manifest.json` committed |
| M1 | Čech coherent cohomology on curves + finiteness | `FiniteDimensional k (H¹ C 𝒪_C)` compiles sorry-free at the pin |
| M2 | Divisors + Riemann–Roch on curves | curve RR theorem sorry-free, genus = h¹(𝒪) |
| M3 | `Sym^d C` as a scheme, smooth | `SmoothOfRelativeDimension d` instance for `Sym^d C` |
| M4 | Construction decision A vs B (priced by M1–M3 actuals) + `Jacobian` def | hole 2 filled |
| M5 | Group law, proper, geom. irred., dim = g | holes 3–6 filled |
| M6 | AJ map + Albanese | holes 1, 7–9 filled; comparator pass |

## Go/no-go (decisive-regime check)

- **Decisive observable:** M1's actual cost (LOC + wall-clock + elaboration
  pain) at the pinned mathlib.
- **Regime where it discriminates:** if M1 lands ≤ ~5k LOC with sane
  elaboration, the arc is viable at subscription budget; if it blows far
  past that, STOP — the obstruction statement goes to the leap queue and
  M1 itself becomes a standalone mathlib-PR contribution instead.
- **Cost of the probe:** M1 itself (bounded; first chip ≈ Čech complex of a
  two-set affine cover).

## Risks / notes

- Kim Morrison (Zulip, 2026-06-09): "multiple groups are working on the
  Jacobian challenge privately." Market: 25% by July, 62% by September.
  Scooping is acceptable (results > recognition); the infrastructure is
  mathlib-PR material either way. Log, don't chase.
- char-p caveats: `h⁰(Ω¹) = h¹(𝒪) = g` holds for smooth proper curves in
  all characteristics (Serre duality), but route choices that flirt with
  `H¹` vs `Ω¹` definitions must check duality availability — mathlib has
  NO Serre duality; prefer `h¹(𝒪_C)` as the primitive.
- The challenge quantifies `C` over `Over (Spec (.of k))` with instance
  hypotheses — no rational point is assumed for the CONSTRUCTION (only
  `ofCurve` takes `P`). Route A's birational arguments classically use a
  rational point / work over `k̄` + descent; this is a real gap to price
  during M4 (Kleiman ch. 9 handles general `k` natively — a point for B).

## M1 API actuals + encoding decision (recorded 2026-06-13, loop run #1)

Pre-M1 grep prerequisite done via GitHub at the pin `5450b53e5ddc` (local
mathlib not yet checked out — bootstrap build still running). Path-level
inventory above is now refined to declaration-level for the M1-relevant
modules:

**`CategoryTheory/Sites/SheafCohomology/Basic.lean`** — abstract sheaf
cohomology `Sheaf.H F n : Type` defined as `Ext`-groups from the constant
abelian sheaf `ℤ`. Coefficients live in **`AddCommGrpCat` (abelian groups)**,
NOT in `ModuleCat k`. Also: `cohomologyFunctor`, `cohomologyPresheaf`,
`H' F n X`, `subsingleton_H_of_isZero`. ⇒ `Sheaf.H` alone gives `H¹ C 𝒪_C`
only as an abelian group, with **no k-module structure** — so it cannot
directly satisfy the M1 DONE WHEN `FiniteDimensional k (H¹ C 𝒪_C)`.

**`CategoryTheory/Sites/SheafCohomology/Cech.lean`** — `cechComplexFunctor :
(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` for a family `U : ι → C` (C has finite
products), valid for **any preadditive `A`**. ⇒ instantiating `A := ModuleCat
k` makes the Čech cochain complex — and hence its homology `H¹` — a **k-module
by construction**. No `Sheaf.H`↔Čech comparison and no `H⁰ ≅ Γ` lemma exist
in the file; both are on us (needed only for genus/RR *correctness*, a later
milestone, not for the M1 DONE WHEN as literally typed).

**`AlgebraicGeometry/Sites/SmallAffineZariski.lean`** — `Scheme.AffineZariskiSite
X := {U : X.Opens // IsAffineOpen U}`; `grothendieckTopology`; `sheafEquiv :
Sheaf (gT X) A ≌ TopCat.Sheaf A X`. ⇒ the scheme↔site bridge for getting
`𝒪_C` (and coherent sheaves) in as Čech input is present.

**`AlgebraicGeometry/Modules/{Presheaf,Sheaf,Tilde}.lean`** — sheaves of
modules on schemes + the `M~` (Tilde) construction on affine schemes; present
but not wired into the cohomology file.

**Absent (unchanged):** coherent finiteness / Serre finiteness, curve RR,
Picard. The deep core of M1 (`FiniteDimensional`) is Serre finiteness — no
short glue.

### Encoding DECISION (resolves the k-module fork)

Define `H¹ C 𝒪_C` as the **degree-1 homology of the two-affine-cover Čech
complex taken in `ModuleCat k`** (`cechComplexFunctor` with `A := ModuleCat
k`), NOT via the abelian-group `Sheaf.H`. This is exactly the route doc's
"computable by Čech on a two-affine cover," and it makes `FiniteDimensional k
(H¹ C 𝒪_C)` type-correct by construction. The Čech↔derived comparison is
deferred to its own milestone (only genus/RR need it).

### M1 decomposition (each its own gated chip)

- **M1a** — Define the two-object Čech complex of `𝒪_C` in `ModuleCat k` via
  `cechComplexFunctor` on a `Fin 2`-indexed affine cover, and define
  `H1 C 𝒪_C := (that complex).homology 1`. Substantive lemma (gate 5):
  identify Čech `H⁰` with the equalizer of the two restriction maps (= global
  sections of the cover), sorry-free. *First, gate-6 check: confirm mathlib
  has no ready `H⁰ ≅ Γ` / equalizer lemma for `cechComplexFunctor` — grep the
  warm local tree.* DONE WHEN: `H1 C 𝒪_C : ModuleCat k` + the H⁰/equalizer
  lemma compile sorry-free at the pin.
- **M1b** — The geometric input: the two-affine cover exists for a smooth
  proper curve (curve minus a closed point is affine; verify the
  geometrically-irreducible-over-arbitrary-`k` form), with its restriction
  and intersection-section maps. DONE WHEN: the cover + maps feeding M1a are
  constructed from the curve's instances, sorry-free.
- **M1c** — Finiteness (the deep core = Serre finiteness for the proper
  curve): `FiniteDimensional k (H1 C 𝒪_C)`. This is the M1 DONE WHEN and the
  go/no-go datum.

### Environment flags (loop run #1, 2026-06-13)

- Local mathlib package dir holds only `.git` — source not yet checked out;
  the bootstrap `lake build` (pid 59568) was still running at ~1h55m. So the
  warm-cache local grep / `lake env lean` iteration is NOT yet available; CI
  on a branch is the working gate (M0 CI runs were green in 3–4 min, so the
  CI-side mathlib cache is warm and fast).
- ⚠️ **Toolchain mismatch:** the running bootstrap (pid 59568) and its child
  `lean` (88311) are `leanprover--lean4---v4.29.0`, but `lean-toolchain`
  pins `v4.30.0-rc2`. Next run: verify the bootstrap is actually building the
  pinned toolchain (`elan show` in-repo, check `.lake` olean target) before
  trusting any local build; if it built 4.29.0 oleans, they are unusable and
  the bootstrap must be re-launched under 4.30.0-rc2.
- **CORRECTION (loop run #2, 2026-06-13):** the above flag was a
  misattribution. pid 59568 (`lsof` cwd) is the **ns-lean-proofs** repo's
  mathlib bootstrap (that repo pins v4.29.0) — *not* alggeo's. In-repo
  `elan show` confirms alggeo is correctly overridden to `v4.30.0-rc2`.
  alggeo's mathlib package dir holds only `.git` (source never checked out),
  so its local bootstrap had simply never started. Run #2 launched a chained
  background bootstrap (waits for pid 59568 to exit — never two concurrent
  `lake build`s — then throttled `lake build` in alggeo, logs `bootstrap.log`).
  Until it finishes, CI on a branch is the gate; jacobian-lean-challenge's
  oleans are NOT reusable (its pin = v4.30.0-**rc1** / mathlib `8e3c9891`).

## ⚠️ M1b survey result (2026-06-13, warm-cache mathlib grep) — the explicit two-affine cover is a MATHLIB GAP; pivot recommended

Gate-6 mathlib-first survey at the pin (`5450b53e5ddc`), run against the now-warm
local checkout. **Decisive finding: the route doc's M1b premise is falsified.**
The premise (this file, M1 section) was "a smooth projective curve minus a point
is affine — classical; verify the geometrically-irreducible-over-arbitrary-`k`
form." Verified result: mathlib at this pin has **none** of the building blocks.

**Present:** `Scheme.OpenCover`/`AffineOpenCover` (`Cover/Open.lean`, indexed by an
arbitrary type `J0`, open immersions); `Proj ℬ`'s `mapAffineOpenCover` (Proj of a
graded ring has an affine cover by `D(f)` charts); `StructureSheaf`;
`PresheafOfModules`/`SheafOfModules` + `restrictScalars` change-of-rings; abstract
`CategoryTheory/Sites/SheafCohomology` (Ext-based).

**Absent (the gap):** "complement of a point/finite set is affine"; any Serre-type
affineness criterion (`isAffine_of_*` hits are all about affine *morphisms*, not
the minus-a-point result); `IsCurve`; a canonical *finite* affine cover of an
*abstract* proper curve `C : Over (Spec k)` given only by its instances. The
challenge curve is NOT handed to us as a `Proj`, so `mapAffineOpenCover` does not
apply without first realizing `C` as a Proj (itself a gap).

**Consequence.** M1b-as-written (instantiate the abstract Čech layer at the curve's
explicit two-affine cover) is blocked behind a major AG sub-arc (construct the
finite affine cover ⇐ "curve minus point affine" ⇐ projectivity + ample/Serre
scaffolding mathlib lacks). This is the **M1 go/no-go signal arriving early** — and
the cheap probe caught it before any cover code was written.

### Route fork (decision needed before more M1 code)

- **(A) Build the cover infrastructure** — prove "smooth proper curve minus a
  closed point is affine" (or a finite affine cover exists) from scratch. Major,
  mathlib-PR-scale; this is the literal `≥ ~5k LOC → convert to mathlib PR`
  branch of the go/no-go. Likely multi-arc on its own.
- **(B) PIVOT — derived-functor sheaf cohomology valued in `ModuleCat k`
  (RECOMMENDED).** Compute `Hⁿ(X, 𝒪_C)` as the right-derived functor of global
  sections, with `𝒪_C` presented as a sheaf of `k`-modules (it is one: forget the
  ring structure, keep the `k`-vector-space structure). `ModuleCat k` is Grothendieck
  abelian (has enough injectives) ⇒ derived functors exist and are **valued in
  `ModuleCat k`** — no explicit finite cover needed, sidestepping the gap entirely.
  The run-#1 encoding fork rejected `Sheaf.H` only because the AddCommGrp-specialized
  form lacks the `k`-module structure; the general *Grothendieck-abelian-target*
  derived-functor route was not considered and likely restores it. NEXT VERIFY: does
  mathlib's sheaf-cohomology API admit a general Grothendieck-abelian coefficient
  category (not just `AddCommGrp`), and does `ModuleCat k` satisfy its hypotheses?
  If yes, M1 (genus = `dim_k H¹`) closes WITHOUT the cover gap, and the M1a Čech
  layer becomes an optional `H⁰`-only convenience (still valid, just not the H¹ route).
- **(C) Reconsider** whether genus/H¹ is reachable at this pin at all (hole 4 forces
  the honest `g`, so "skip it" is not available — the comparator's universal property
  is the no-cheating clamp).

**Recommendation: B.** It is the only fork that doesn't front-load a multi-arc
mathlib gap, and it directly serves the M1c DONE WHEN (`FiniteDimensional k H¹`).
The next investigation chip is a *survey*, not code: confirm `ModuleCat k`-valued
derived sheaf cohomology is expressible at the pin. If B is viable, M1a's
`cechHZeroIsoEqualizer` is preserved as `H⁰` content but the H¹/genus route moves
to derived functors.

## 🛑 M1 GO/NO-GO VERDICT (2026-06-13) — NO-GO for a loopable chip sequence; the real wall is the coherent-cohomology stack

Following the cover-gap finding, the deeper survey traced the genus to its true
prerequisite and confirmed the wall across **all of mathlib** at the pin:

- Hole 4 (`smoothOfRelativeDimension_genus`) forces `genus C = dim_k H¹(C, 𝒪_C)`,
  i.e. the M1c DONE WHEN `FiniteDimensional k H¹` is unavoidable.
- `FiniteDimensional k H¹(proper curve, 𝒪)` **is Serre's finiteness theorem** for
  coherent cohomology of a proper scheme.
- **Confirmed absent from the entire pinned mathlib (`5450b53e5ddc`):**
  `QuasiCoherent` sheaves (zero occurrences anywhere), coherent sheaves, Serre
  finiteness, scheme sheaf cohomology, and any `Ext`/cohomology wired on
  `SheafOfModules`. The abstract substrate exists (`Sheaf.Γ J A` general global
  sections; `ModuleCat k` Grothendieck-abelian with enough injectives;
  Grothendieck-abelian ⇒ `HasExt`), so H¹ can be *defined* as a `k`-module via
  fork B — but **finiteness** has no foundation to stand on.

**Verdict.** The alggeo Jacobian challenge is reachable only after building the
coherent-cohomology-of-schemes stack: quasi-coherent → coherent sheaves →
cohomology → Serre finiteness → (for dim = g) Riemann–Roch-grade results. That is
a major, multi-month **mathlib-infrastructure program**, not a chip sequence an
autonomous 7-minute loop can close. The decisive-regime-reachability check
(`feedback_decisive_regime_reachability`) therefore returns **NO-GO for the loop**;
escalate the scope decision to Bryan.

**Forks for Bryan (scope decision, not a Lean chip):**
- **(I) Commit to the infrastructure arc** — build quasi-coherent/coherent
  sheaves + cohomology + Serre finiteness as a real program. Every piece is prime
  mathlib-PR material (large upstream value; `feedback_mathlib_work_is_in_scope`).
  Months, human-architected, not loopable.
- **(II) Incremental upstream** — land the bounded, already-clean pieces as
  standalone mathlib PRs now (the M1a Čech-in-`ModuleCat k` layer; `underToModuleCat`),
  building toward the challenge without committing to finish it soon.
- **(III) Shelve** the alggeo challenge; record it as gated on the coherent-cohomology
  milestone.

**Salvage (already verified, compile-clean, upstreamable — the few hours were not
wasted):** `Submission/CechModuleCat.lean` (abstract Čech cohomology valued in a
preadditive/`ModuleCat k` target + `H⁰ ≅ equalizer` sheaf condition) and
`Submission/StructureSheafModule.lean` (`underToModuleCat`, the `Under R ⥤ ModuleCat R`
forgetful absent from mathlib). ~170 LOC of genuine infrastructure.

The loop is DISABLED and a `LOOP_HALT` is in place pointing here, so no autonomous
run thrashes against this wall.

## ✅ Segment 1 results + route corrections (2026-06-13, continuous-driving session, full-build green)

Built `Submission/SheafCohomologyModuleCat.lean` (derived-functor / fork-B route):
`H J k n F := Ext (coeffSheaf J k) F n` valued in `ModuleCat k` (a `k`-module via
`Ext.instModule`), with `HZeroAddEquivΓ : H J k 0 F ≃+ Γ(F)` (degree-0 cohomology =
global sections, the `H⁰ ≅ Γ` mathlib lists as a TODO for `Sheaf.H`). New helper:
`Functor.const_additive`. Sorry/axiom-clean, vacuity-lint 0, throttled full `lake
build` green (8319 jobs).

**Correction 1 — the cohomology foundation is ALREADY in mathlib at the pin.**
The Gate-6 warm-cache survey found `Abelian/GrothendieckAxioms/Sheaf.lean` gives
`IsGrothendieckAbelian (Sheaf J A)` (small site, `A` Grothendieck-abelian,
`[HasSheafify J A]`), and `Abelian/GrothendieckCategory/HasExt.lean` gives
Grothendieck ⇒ `HasExt`. So `HasExt (Sheaf J (ModuleCat k))`, `Linear k (Sheaf J
(ModuleCat k))`, and `Module k (Ext …)` all resolve with no new content. The
NO-GO verdict's "the abstract substrate exists … but finiteness has no
foundation" was right about finiteness but understated how much of the *defining*
layer is free: segment 1's "first real content" (build Grothendieck-abelian-of-
sheaves) did not need building. The k-module structure on cohomology is likewise
free (no need to land in a bundled `ModuleCat k` object; the bare `Ext` type's
`Module k` suffices for `FiniteDimensional k`).

**Correction 2 — genus has no required equation; cohomology serves only hole 1.**
`genus C : ℕ` (hole 1) is a bare `def`; hole 4 only consumes it as
`SmoothOfRelativeDimension (genus C) (Jacobian C).hom`. Holes 2,3,5,6,7,8,9 (the
Jacobian/Albanese construction + universal property) are the FGA-grade bulk with
no mathlib foundation. The cohomology stack does not touch them. This sharpens the
NO-GO/decisive-regime point: the arc's wall is Jacobian representability, not
Serre finiteness. See `OPEN.md` / `NEXT_SESSION.md` "Scope reality".

**Residual on Segment 1 (precise):** `HZeroAddEquivΓ` is an `AddEquiv`, not a
`k`-`LinearEquiv`. The linear upgrade needs `Functor.Linear k (Sheaf.Γ J (ModuleCat
k))`, for which mathlib has no off-the-shelf "right adjoint is linear" lemma
(`Adjunction.right_adjoint_additive` exists but only additive; `lim` is not a
registered `Functor.Linear`). Tractable but its own small piece; not needed for
the genus (which uses `H¹` finrank, not `H⁰`).

## ✅ Segment 2 results + hole 1 filled (2026-06-13, continuous-driving session, full-build green)

Built `Submission/StructureSheafCohomology.lean`: `𝒪_C` presented as a sheaf valued
in `ModuleCat k` on the *opens site* of `C.left`, fed to Segment 1's `H` to give
`H1 C = H¹(C, 𝒪_C)` as a `k`-module; `genusH1 C := Module.finrank k (H1 C)`; and
`Submission.genus` fills `Challenge.lean` hole 1 with it (signature byte-compatible —
`@Submission.genus = @JacobianChallenge.genus` typechecks — sorry/axiom-clean,
vacuity-lint 0, full `lake build` green, 8320 jobs).

**The handoff's feared Segment-2 blockers did not materialise** (Gate-6, warm cache):
- The curve's opens site `Opens.grothendieckTopology C.left` is a `SmallCategory`
  (preorder) and `HasSheafify (Opens.gt) (ModuleCat k)` **resolves automatically**
  (general instance: `forget` preserves limits + small covers). So neither an
  `EssentiallySmall` bridge nor a `HasSheafify` hypothesis-discharge was needed — the
  opens site feeds `H` directly. (`SmallAffineZariski`/`sheafEquiv` were not needed.)
- The `ModuleCat k`-valued sheaf condition transports from `C.left.IsSheaf` for free:
  `structurePresheafModule C ⋙ forget (ModuleCat k)` is *defeq* to `C.left.presheaf ⋙
  forget CommRingCat` (same underlying `Type`-presheaf), and `forget (ModuleCat k)`
  reflects limits (`isSheaf_of_isSheaf_comp`). No bespoke gluing.
- The structure-sheaf `k`-algebra lift is `Under.mk (kStruct.app U) ⋙ underToModuleCat`,
  reusing Segment 1b's forgetful. `kStruct` is the only genuinely new geometric content
  (`const k ⟶ 𝒪_C` from the structure morphism + restriction).

**Net:** the entire fork-B cohomology of the curve carries **zero** typeclass
hypotheses. The k-module H¹ route the NO-GO verdict called merely "definable" is now
*defined and wired to the challenge* (hole 1).

**Remaining (unchanged):** Segment 3 = `FiniteDimensional k (H1 C)` (Serre finiteness)
has no mathlib foundation — the major sub-arc. And holes 2,3,5,6,7,8,9 (the Jacobian/
Albanese) remain the FGA-grade bulk. Hole 1 filled is 1 of 9; the genus *value* is not
certified until Segment 3.

## TOWER A — Segment-3 finiteness obstruction map (compile-verified, 2026-06-13 parallel session)

5-agent mathlib survey + compile-probes located the **exact** absent foundations between
the submission's `H1 C = Ext (coeffSheaf) (structureSheafModule C) 1` (in
`Sheaf (Opens.gt C.left) (ModuleCat k)`) and `FiniteDimensional k (H1 C)`. Two
independent walls, both genuinely absent (not a grep miss — probed):

**Wall 1 — H¹ finiteness proper = the local-to-global / derived↔Čech comparison.**
mathlib HAS the finiteness *primitive* `ModuleCat.finite_ext` (`Ext` of f.g. modules over a
Noetherian ring is f.g., `Algebra/Category/ModuleCat/Ext/Finite.lean`) and the quasi-coherent
sheaf layer (`SheafOfModules.IsQuasicoherent/IsFiniteType/IsFinitePresentation`,
`Scheme.Modules`, `IsLocallyNoetherian`). But `finite_ext` lives in `ModuleCat R` while `H1 C`
is `Ext` in the *sheaf* category; the bridge (sheaf-`Ext` computed locally via module-`Ext`,
glued) — i.e. derived↔Čech for an affine cover, or proper-pushforward finiteness — is
**confirmed absent** (no comparison theorem, no Leray, no acyclic-cover theorem,
`Sites/SheafCohomology/*`). This bridge *is* Serre finiteness; multi-month.

**Wall 2 — even the "easy" h⁰ is blocked on `smooth/field ⇒ reduced`.** Compile-probe verified
the whole `IsIntegral C.left ⇒ Γ(C,⊤) finite over k` chain INFERS at the pin
(`finite_appTop_of_universallyClosed`, `isField_of_universallyClosed`, `Spec k` one-point,
`IrreducibleSpace C.left` via `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`,
reduced+locally-Noetherian base) EXCEPT one link: **`GeometricallyReduced C.hom` from
`Smooth`**, which needs **`smooth-over-a-field ⇒ reduced`** — absent at BOTH scheme and ring
level (no `smooth⇒regular`, no `IsGeometricallyReduced` producer from smoothness; bottoms out
in `Jacobian/standard-smooth ⇒ regular local ring` and `regular ⇒ domain`, both absent —
`RegularLocalRing/Defs.lean` has only the criterion, not these producers). Deep CA sub-arc.

**Plus** the k-linear cohomology layer (prerequisite for `finrank`/`FiniteDimensional` to be
meaningful on `H⁰`): `Sheaf.Γ`/`constantSheaf` lacked `Functor.Linear k`, and
`Adjunction.homLinearEquiv` was absent — all bounded *category-theory* gaps (not deep CA).

**Built this session (green, sorry/axiom-free, vacuity-lint 0, fork-II upstreamable):**
`Submission/Cohomology/LinearH0.lean` — `CategoryTheory.Adjunction.{homLinearEquiv,
right_adjoint_linear, left_adjoint_linear}`, the `Functor.Linear` analogues of mathlib's
additive adjunction lemmas. (The downstream `HZeroLinearEquivΓ` assembly is one
`ModuleCat`-carrier `SMulCommClass` synth-quirk from landing; deferred.)

**Verdict:** Tower A's genus-finiteness goal is a genuine multi-month CA/AG infrastructure
program (Walls 1 + 2), NOT a single-session deliverable. Decisive-regime check: the decisive
observable (a green `FiniteDimensional k (H1 C)`) is unreachable without building absent
foundations. Leap-queue items: (i) `smooth/field ⇒ reduced` (⇐ `Jacobian ⇒ regular local
ring` + `regular ⇒ domain`); (ii) derived↔Čech / proper-pushforward finiteness comparison.

### TOWER A — round-2 brick: `regular ⇒ domain` in ALL dimensions (2026-06-13, `main` @ `5d3a8ed`, pushed)

The `regular ⇒ domain` half of Wall 2's leap-queue item (i) is now **built in arbitrary
dimension** — `Submission/Cohomology/RegularLocalDomainGeneral.lean` (336 LOC, green:
`lake build` 8335 jobs exit 0; axioms = `propext`/`Classical.choice`/`Quot.sound` only;
vacuity-lint 0; independently re-verified). Round 1's `RegularLocalDomain.lean` only did
`dim ≤ 1` (principal-`𝔪` `tᵏ·unit` factorisation, which does not extend to `dim ≥ 2`).

- **Theorem 1** `spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le` — the cotangent /
  embedding-dimension drop: `x ∈ 𝔪 \ 𝔪² ⇒ spanFinrank 𝔪(R/(x)) + 1 ≤ spanFinrank 𝔪(R)`. Route:
  `CotangentSpace.span_image_eq_top_iff` generating-set criterion (complement of `κ·x̄`, lift a
  basis, `Ideal.map_span`) — sidesteps residue-field rank-nullity. Independently reusable.
- **Theorem 2** `isDomain_of_isRegularLocalRing` (Stacks 00NP) — strong induction on embedding
  dim: prime avoidance (`Ideal.subset_union_prime_finite` over `Option (minimalPrimes R)`, `𝔪²`
  the lone non-prime exception) for the parameter; `R/(x)` regular of dim −1 via Thm 1 + the
  present `supportDim_quotSMulTop_succ_eq_…` parameter dim-drop; IH ⇒ `(x)` prime; Nakayama on a
  minimal prime `q ≤ (x)` ⇒ `q = ⊥` ⇒ `⊥` prime ⇒ `IsDomain`.

**This is foundation, NOT a hole-fill** (gates-honest): it closes the `regular ⇒ domain` leaf of
Wall 2 but the *remaining* Wall-2 gap — **`smooth/standard-smooth ⇒ regular local`** — still
bottoms out in two absent pieces, both compile-verified absent at the pin with the warm cache:
1. **the finite-type-over-field dimension formula** (`ringKrullDim` of a standard-smooth local
   `k`-algebra `= rel dim`). `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`dim k[x₁..xₙ] = n`)
   and the regular-sequence dim-drop (`ringKrullDim_add_length_eq_…_of_isRegular`) exist, but
   `KrullDimension/Field.lean` has only `dim field = 0` — **no `dim = trdeg`, no dim of a
   finite-type/essentially-finite-type local algebra over a field**. Assembling it for the
   localized standard-smooth presentation is its own multi-piece arc.
2. **the residue-field-aware cotangent (Zariski-tangent) computation** `finrank_κ(𝔪/𝔪²) = rel dim`
   — needs the conormal sequence `𝔪/𝔪² → Ω_{S/k}⊗κ → Ω_{κ/k} → 0` with the `Ω_{κ/k}` correction
   for `κ/k` non-separable/non-trivial (the genuine delicacy of `smooth ⇒ regular` over an
   arbitrary base). `StandardSmoothCotangent` gives `rank_S Ω[S⁄R] = rel dim` (an `S`-module
   fact), NOT the Zariski cotangent `finrank_κ`; the two `CotangentSpace` notions
   (`IsLocalRing.CotangentSpace = 𝔪/𝔪²` vs `Extension.CotangentSpace = S⊗Ω`) are distinct.

So the updated Wall-2 leap-queue item (i) is sharper: `smooth/field ⇒ reduced` now reduces to
`smooth ⇒ regular`, which reduces to the two leaves above (`regular ⇒ domain` ✓ done). Wall 1
(Serre finiteness / derived↔Čech) unchanged. All 9 holes remain OPEN — this brick certifies no
hole; it is upstreamable mathlib content completing the regular-local-ring theory.

## 🅱️ TOWER B survey — Jacobian construction (holes 2,3,5,6,7,8): declaration-level inventory + priced Route-A-vs-B decision (2026-06-13)

Tower B's mandate = **construct `Jacobian C` (= Pic⁰)** with group structure (hole 3),
properness (5), geometric irreducibility (6), Abel–Jacobi `ofCurve` (7), `comp_ofCurve`
(8), the def itself (2). Per the brief: survey mathlib for the independent core (finite-
group quotient of a quasi-projective scheme → `Sym^d C`), price Route A vs B, and STOP +
state the obstruction if the core blows past ~5k LOC. This section is that survey, run at
**declaration level** against the warm pinned mathlib (`5450b53e5ddc`, read-only canonical
tree). It is the decisive-regime datum; the construction is a multi-month program and the
A-vs-B choice is a leap-queue item for Bryan (see `noethersolve/docs/LEAP_QUEUE.md §4`).

### Declaration-level mathlib inventory for the construction

**Present (usable substrate):**
- `GrpObj` group objects: `CategoryTheory/Monoidal/Cartesian/Grp_.lean` (hole-3 target type).
- **Some abelian-variety theory already exists:** `AlgebraicGeometry/Group/Abelian.lean` —
  `isCommMonObj_of_isProper_of_geometricallyIntegral` (**stacks 0BFD**: a proper
  geometrically-integral group object is commutative) and `η[G].left` is a closed
  immersion. `Group/Smooth.lean` likewise. (Mostly Tower C's lane, but it means holes
  5/6 + commutativity are *consumers* of, not blocked by, this file.)
- Scheme **coproducts** `HasColimitsOfShape (Discrete σ) Scheme` (`Limits.lean:187`),
  **gluing** (`Gluing.lean`), `AffineScheme`, `Proj ℬ` + `mapAffineOpenCover`,
  `FunctionField`, `Geometrically/*`, `Morphisms/{Flat,Descent,…}`.
- Invariant-ring substrate: `FixedPoints.subalgebra A B H` / `FixedPoints.subring`
  (`FieldTheory/Fixed.lean`, `Algebra/Ring/Action/Invariant.lean`), the finite-group
  **characteristic polynomial** + **integrality** `Algebra.IsInvariant.isIntegral`
  (`RingTheory/Invariant/Basic.lean:138,175`: `B` integral over its invariants for finite
  `G`), and **Artin–Tate** `Algebra.fg_of_fg_of_fg [IsNoetherianRing A]`
  (`RingTheory/Adjoin/Tower.lean:145`).

**Absent (the construction layer — ALL on us, zero matches at the pin):**
- **`Sym^d` / symmetric power of a scheme** — `grep symmetricPower|symmetricProduct` over
  `AlgebraicGeometry/` = **0 hits**.
- **Quotient of a scheme by a finite group action** — no `geometricQuotient` /
  `categoricalQuotient` / GIT; the only `MulAction`-on-AG hits are
  `EllipticCurve/VariableChange` (change-of-coords group on Weierstrass *data*, not a
  quotient scheme).
- **`Scheme` has NO coequalizers** — `Limits.lean` registers only `Discrete σ` colimits;
  so a quotient `X → X/G` **cannot** be obtained as a categorical colimit and must be
  hand-built (Spec-of-invariants, glued).
- Noether **finiteness of invariants** (`B^G` finite-type over `k`; `B` module-finite over
  `B^G`) — mathlib has only the NT-Galois-of-integers `Algebra.IsInvariant` flavor and the
  `Rep`-module `invariants` (`RepresentationTheory/Invariants.lean` = `Submodule`, not a
  subalgebra-finiteness). The integrality half IS present; the FG/module-finite half is the gap.
- "complement of a finite set / orbit lies in an affine open" for a quasi-projective scheme
  (the `S_d`-invariant affine cover of `C^d`); curve **divisors / Riemann–Roch**;
  **birational group law** extension; Picard functor/scheme; representability of Pic⁰.

### First foundational gap (Route A core) decomposed — the ≥5k-LOC wall, reached immediately

`Sym^d C := C^d / S_d` as a **smooth projective scheme** factors into, in dependency order:

| Piece | Statement | mathlib at pin | Cost class |
|---|---|---|---|
| P1 | **Noether finiteness of invariants**: finite `G` on finite-type `k`-algebra `B` ⇒ `B^G` finite-type/`k`, `B` module-finite/`B^G` | integrality ✓, FG-half ✗ | **bounded** (~100–300 LOC; Artin–Tate + integral+FT⇒finite both present) |
| P2 | **Affine quotient scheme** `Spec(B^G)` + universal property = categorical quotient of `Spec B` by `G` among *all* schemes | ✗ (no coequalizers) | medium (Γ⊣Spec + factorization gluing) |
| P3 | **`G`-invariant affine cover** of a quasi-projective `X` (⇐ every orbit lies in an affine open ⇐ quasi-projectivity) | ✗ (no orbit-in-affine, no ample/embedding scaffolding) | **hard** (mathlib-PR-scale on its own) |
| P4 | glue affine quotients → quotient scheme `X/G` with quotient map | ✗ | medium (needs P2+P3) |
| P5 | `Sym^d C` smooth + projective (`C` proper smooth curve ⇒ projective; `Sym^d` smooth via the discriminant / étale-local `Sym^d 𝔸¹ ≅ 𝔸^d`) | ✗ | **hard** |

Even with P1 free, **P3 and P5 are each independent multi-arc mathlib gaps**, and `Sym^d C`
is only the *input* to the birational group law (hole 3) and Abel–Jacobi (hole 7). The
decisive-regime threshold ("core blows far past ~5k LOC ⇒ STOP") is crossed at P3 — i.e. at
the *first* foundational gap, before any of the six holes is touched.

### Priced Route A vs Route B (critical paths)

- **Route A (Weil / `Sym^d`, Milne JV §§2–7):** P1→P5 above **+** curve Riemann–Roch (for
  the birational group law) **+** the birational-group-law extension theorem (BLR ch.5 /
  Serre GACC §V) **+** the **no-rational-point gap** (the challenge curve carries no assumed
  `k`-point for the *construction*; Route A's birational arguments classically need a point
  or work over `k̄` + Galois descent — a genuine extra arc). ≈ 6–7 hard sub-arcs.
- **Route B (FGA Pic⁰ representability, Kleiman ch.9):** Hilbert/Quot (FGA ch.5–7) +
  flattening stratification + cohomology-and-base-change (Mumford AV §5) + representability
  of Pic⁰ + deformation theory (smoothness + `dim = g`). Deeper trunk, but **native over
  general `k`** (no rational-point gap, no `Sym^d`, no finite-quotient infra), and maximally
  reusable / PR-able. ≈ 5 very deep sub-arcs.

**Verdict (Tower B).** Both routes are multi-month, human-architected mathlib-infrastructure
programs; **neither closes any of holes 2,3,5,6,7,8 in a single session.** The construction
is NOT reachable at subscription budget without first building either the finite-quotient
stack (A) or the Hilbert/Quot + base-change stack (B). The Route-A-vs-B decision is itself
the leap-queue datum: lean **B** if the goal is the reusable trunk + no-point robustness;
lean **A** only if a rational point can be assumed/added and RR lands cheaply from Tower A.

### Fork-II action taken this session (bounded, route-independent, upstreamable)

Per "land the bounded clean pieces as standalone mathlib PRs rather than grinding": **P1
(Noether finiteness of invariants)** is built as `Submission/Jacobian/InvariantFiniteness.lean`
— it is independently valuable to mathlib (a missing classical theorem, Emmy Noether 1926),
route-independent (a PR even if the challenge takes Route B), and bounded by the present
Artin–Tate + integrality + `integral+finite-type⇒module-finite` lemmas. It does **not**
commit the challenge to Route A and is **not** a renamed sorry (gate 7(c): a substantive
classical lemma milestone M3 consumes; gate 5: substantive plain-math statement). P3/P5 and
the route decision are stated above for the human leap, not ground past solo.

## ✅ TOWER B build — the AFFINE core of M3 (finite-group quotient + symmetric power), 2026-06-13

Following the survey, the **affine** model of milestone M3 was built in full (route-independent,
fork-II, upstreamable). 7 modules under `Submission/Jacobian/`, **565 LOC**, all sorry-free +
axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only) + vacuity-lint 0, full throttled
`lake build` green (8327 jobs). Commits `a4bff85`, `d61c7c0`, `92205b2` on
`tower/jacobian-construction` (pushed; CI cross-check).

- `InvariantFiniteness.lean` — **Noether finiteness of invariants** (P1): for finite `G` on a
  finite-type `R`-algebra `B`, `B` is module-finite over `B^G`, and (R Noetherian) `B^G` is
  finite-type over `R`. (Artin–Tate + `Algebra.IsInvariant.isIntegral` + `Algebra.IsIntegral.finite`.)
- `AffineInvariants.lean` — `B^G` as the equalizer of the `G`-action (mem characterization,
  injectivity of `B^G ↪ B`, the ring-level universal factorization `exists_lift_of_invariant`).
- `AffineQuotient.lean` — **the affine finite-group quotient `Spec(B^G)` of `Spec B`** (generic in
  `(R, B, G)`, `G` in its own universe): the quotient morphism `π`, with `π` integral (⇒
  `UniversallyClosed`), finite (⇒ `IsProper`) when `B` finite-type, **`G`-invariant**
  (`specAction g ≫ π = π`), and the **categorical-quotient universal property for affine targets**
  (`exists_unique_lift_of_invariant`) — built by hand through the `Γ ⊣ Spec` adjunction since
  `Scheme` has no coequalizers.
- `SchemeGroupAction.lean` — the lifted `specAction g` form a genuine functorial `G`-action
  (`specAction_one`, `specAction_mul`, each `specAction g` an `IsIso`).
- `TensorPowerPermAction.lean` — **`MulSemiringAction (Equiv.Perm (Fin d)) (A^{⊗d})`** by `R`-algebra
  automorphisms permuting tensor factors (multiplicativity proved by induction on pure tensors) +
  `SMulCommClass`. This is the permutation action mathlib lists as a **TODO**
  (`LinearAlgebra/TensorPower/Symmetric.lean`).
- `TensorPowerFiniteType.lean` — `A^{⊗d}` is finite-type over `R` when `A` is (slot inclusions
  `singleAlgHom k` + `tprod f = ∏ k singleAlgHom k (f k)` + pure tensors span), a global instance
  ⇒ the symmetric-power finiteness is **unconditional**.
- `AffineSymmetricPower.lean` — **`Sym^d(Spec A) = Spec((A^{⊗d})^{S_d})`**, by instantiating
  `AffineQuotient` at `B = A^{⊗d}`, `G = S_d`: integral / universally-closed / finite / proper /
  `S_d`-invariant / universal-property, all inherited.

**Scope honesty (unchanged).** This is the AFFINE model. None of holes 2,3,5,6,7,8 is filled: the
challenge curve `C` is **projective, not affine**, so `Jacobian C` still needs the two route-doc
walls that remain genuinely open at the pin — **P3** (an `S_d`-invariant *affine cover* of the
quasi-projective `C^d`, ⇐ "an orbit lies in an affine open", absent) and **P5** (`Sym^d C` smooth +
`C` projective), then the birational group law (RR) and the no-rational-point descent. The affine
stack is the foundation those glue onto, and is prime mathlib-PR material on its own (esp. the
`S_d`-on-`A^{⊗d}` action and the affine finite-group quotient). Recorded for the human leap.

## SHARED-FOUNDATION brick I.1a — the internal-hom wall, traced to its leaves (2026-06-13, warm cache)

**Target.** Discharge `(sheafificationW J R₀).IsMonoidal` (the one undischarged hypothesis of
`SheafOfModulesMonoidal.lean`'s `SheafOfModules.monoidalCategory`), making `MonoidalCategory
(SheafOfModules R)` unconditional → unblocks I.2 (invertible sheaves → `Pic X`), the shared
bottom of BOTH Jacobian routes.

**What `IsMonoidal` actually requires.** By `IsMonoidal.mk'`
(`Localization/Monoidal/Basic.lean:50`): for `f,g` morphisms of presheaves of modules with
`toPresheaf f, toPresheaf g ∈ J.W`, show `toPresheaf (f ⊗ₘ g) ∈ J.W`. Equivalently the two
whiskering fields `W g ⟹ W (F ◁ g)` and `W f ⟹ W (f ▷ G)`.

**The general `inverseImage` instance does NOT apply.** `Localization/Monoidal/Basic.lean:71`
gives `(W.inverseImage F).IsMonoidal` for FREE — *but only when `F` is a strong monoidal functor*
(`[F.Monoidal]`). Here `F = PresheafOfModules.toPresheaf`, which is **not** monoidal: the tensor
on `PresheafOfModules` is the pointwise `· ⊗[R.obj X] ·` over the ring, while the target's tensor
is `⊗_ℤ`; `toPresheaf (M ⊗_R N) ≠ toPresheaf M ⊗_ℤ toPresheaf N`. (And the canonical surjection
`M ⊗_ℤ N ↠ M ⊗_R N` is *not* in `J.W`, so 2-out-of-3 against the ab-group monoidality cannot
bridge them.) This is exactly the gap.

**What `J.W` IS, and why the clean route needs an internal hom** (`Sites/Localization.lean`:
`J.W := ObjectProperty.isLocal (Presheaf.IsSheaf J)`). So `J.W g ↔ ∀ H, IsSheaf J H → Bijective
(precompose g into H)` — orthogonality to sheaves. Mathlib's own `(J.W).IsMonoidal` instance
(`Sites/Monoidal.lean:149`, for presheaves valued in a *braided closed* `A`) proves `whiskerLeft`
(`:132`) precisely by this orthogonality + the **closed structure**: `Hom(F⊗Gᵢ, H) ≅ Hom(Gᵢ,
[F,H])` and `[F,H]` is a sheaf when `H` is (`isSheaf_functorEnrichedHom`, `:102`). To replicate
this for presheaves of modules I need the analogue: a **concrete internal hom `[F,H]` of
presheaves of modules** + the tensor-hom adjunction + **`[F,H]` is a sheaf when `H` is**.

**Absent at the pin, and deliberately so.** No `MonoidalClosed`/`ihom`/internal-hom on
`PresheafOfModules` or `SheafOfModules` (grep, ModuleCat tree: only `ModuleCat/Monoidal/Closed.lean`,
the *fixed-ring* internal hom). Mathlib's `Sites/Monoidal.lean` machinery (`Enriched.FunctorCategory`,
`functorEnrichedHom`, `MonoidalClosed (Cᵒᵖ ⥤ A)`) is for **plain functor categories with constant
enrichment** — it does not port to presheaves of modules, where the enriching ring `R.obj X`
*varies with X*. The varying-ring internal hom is the single hardest object in sheaf-of-modules
theory and is exactly what mathlib omits.

**Two non-routes (checked, ruled out):**
1. **SAFT shortcut → abstract `MonoidalClosed`.** `tensorLeft F` preserves all colimits
   (`Presheaf/Monoidal.lean:237`); `PresheafOfModules` has a small separating set
   (`Generator.lean:85`, `freeYoneda`) and is `WellPowered` (`:96`). So
   `isLeftAdjoint_of_preservesColimits_of_isSeparating` (`Adjunction/AdjointFunctorTheorems.lean:119`,
   modulo `WellPowered Cᵒᵖ`) yields a right adjoint to each `tensorLeft F` abstractly ⇒
   `MonoidalClosed (PresheafOfModules R)` as a standalone instance. **But this does NOT discharge
   I.1a:** the abstract SAFT adjoint carries *no formula*, and the whiskerLeft proof needs "`[F,H]`
   is a sheaf", which is provable only from a *concrete* pointwise internal hom. The SAFT
   `MonoidalClosed` is a clean, bounded, genuinely-new mathlib PR (fork II) — but it is **off the
   critical path** for `W.IsMonoidal`.
2. **Direct local-bijectivity route.** `J.W h ↔ IsLocallyInjective ∧ IsLocallySurjective`
   (`J.WEqualsLocallyBijective`). Local *surjectivity* of `F ⊗ g` from `g` loc-surj is provable
   (generators + cover refinement). Local *injectivity* of `F ⊗ g` is **FALSE in general** from
   `g` loc-injective alone (tensor is not left exact: `·2 ⊗ ℤ/2` kills `ℤ/2`); it needs `g ∈ W`
   (loc-*iso*), and the only non-circular way to use loc-iso here routes back through
   sheafification-commutes-with-tensor — i.e. the theorem itself. Dead end without the internal hom.

**Conclusion / entry point.** I.1a = **build the concrete internal hom of presheaves of modules
over a varying commutative ring presheaf**: object `[F,H](U) := ` (homs of the restricted
presheaves of modules over `R|_U`), the `R.obj U`-module + restriction-functoriality structure,
the adjunction `Hom(F ⊗_R G, H) ≅ Hom(F, [G,H])`, and `IsSheaf H ⟹ IsSheaf [F,H]`. Then the
~30-line port of `Sites/Monoidal.lean`'s `whiskerLeft`/`whiskerRight`/`monoidal`. This is a
multi-hundred-LOC, multi-session foundational arc (genuinely new mathlib content, not a paraphrase
or renamed `sorry`), and it reaches only as far as I.2 (`Pic X`) — still below the **deferred A-vs-B
route leap** (`LEAP_QUEUE §4`) and the FGA-grade Jacobian construction (holes 2–9). Logged in
`LEAP_QUEUE §6` for the build/pivot decision.

### I.1a BUILD (Bryan: "Build I.1a now", 2026-06-13) — piece (I) DONE; decomposition + handles

`Submission/Cohomology/PresheafOfModulesInternalHom.lean`. Proof mirrors mathlib's
`GrothendieckTopology.W.monoidal` (`Sites/Monoidal.lean`). Three pieces + a port:

- **✅ Piece (I) — `sheafificationW = ObjectProperty.isLocal (· ∈ range (localInclusion α).obj)`**
  (`sheafificationW_eq_isLocal`) + the consumable form `sheafificationW.bijective_precomp`
  (for `W g` and any sheaf-of-modules `H`, precomposition with `g` is a bijection into
  `(localInclusion α).obj H`). `lake env lean`-clean, exit 0. KEY HANDLES:
  `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`
  (`SheafOfModules/Localization.lean`: `W = (isomorphisms).inverseImage (sheafification α)`)
  + `ObjectProperty.isLocal_eq_inverseImage_isomorphisms` (`Localization/Bousfield.lean`)
  applied to `sheafificationAdjunction α`, whose **right adjoint
  `F = SheafOfModules.forget R ⋙ restrictScalars α` is fully faithful** (`Sheafification.lean`
  lines 168–172, from `IsIso counit`). Local objects = exactly `F.obj H`, restrictions of sheaves.
- **Piece (III) — `[F,H]` is a sheaf when `H` is.** Mirror `Presheaf.IsSheaf.hom`
  (`Sites/SheafHom.lean`: `presheafHom F G` is a sheaf when `G` is, for *any* target category).
  Underlying type-presheaf of `[F,H]` is (a sub, cut by `R`-linearity, of)
  `presheafHom (toPresheaf F) (toPresheaf H)`; carry it through `forget`-reflects-limits.
  Depends on the piece-(II) object.
- **Piece (II) — concrete internal hom + tensor-hom adjunction (THE BULK).** Build
  `[F,H] : PresheafOfModules R₀'` with `[F,H].obj X = R(X)`-module of PMod-morphisms
  `F|_{Over X} ⟶ H|_{Over X}`, restrictScalars-compatible restriction maps, and
  `Hom_PMod(F ⊗_R G, H) ≅ Hom_PMod(G, [F,H])` natural in `G` (= `Closed F` ⇒
  `MonoidalClosed (PMod R₀')`; def `Monoidal/Closed/Basic.lean`: `Closed X = {rightAdj, adj}`).
  Over-restriction handles: `PresheafOfModules.pushforward₀`/`Sites/Over.lean`;
  `SheafOfModules/PushforwardContinuous.lean`'s `M.over X` (sheaf version) as a model. SAFT
  (`isLeftAdjoint_of_preservesColimits_of_isSeparating`, with `tensorLeft F` colimit-preserving +
  `freeYoneda` separator + `WellPowered`) gives the adjoint *abstractly* but formula-free → cannot
  feed piece (III); must build concretely.
  - **✅ OBJECT DONE (2026-06-13, `main` @ `1a6d06e`, full build 8341 jobs, vacuity 0, axioms
    clean).** `internalHomObj F H X : ModuleCat (R₀.obj X)` = `[F,H](X)` = the `R₀(X)`-module
    `(restrict X).obj F ⟶ (restrict X).obj H` (slice-restrictions via `pushforward₀ (Over.forget
    X.unop)`), with the full `Module (R₀.obj X)` instance. **THE INSTANCE-DIAMOND WALL FELL** (it was
    the real blocker, not the slice machinery): scaling a `ModuleCat (R₀'.obj _)` morphism — OR its
    underlying `LinearMap` — by a ring element fails `synthInstance`, because morphism-scaling needs
    `SMulCommClass`/`Linear`/`Module S (LinearMap)` over the **RingCat** carrier `R₀'.obj _`, which is
    not found (defeq-but-not-syntactic vs the canonical instance); whereas **element**-scaling is
    mathlib-provided as `Module (R₀.obj X) (M.obj X)` (`Presheaf.lean`) over the **CommRingCat**
    carrier. RESOLUTION = **carrier discipline**: build the scaled morphism `internalSMulApp`
    *element-wise* as a `LinearMap` typed over the CommRingCat carrier `R₀.obj (op W.left)`
    (`fun x => R₀(W.hom)(r) • φ.hom x`), where `map_smul'` closes by `smul_comm`. `internalHomSMul`
    wraps it as a PMod-morphism; its naturality reduces to the scalar restriction-compat
    `(S.map g)(R₀(W.hom)(r)) = R₀(W'.hom)(r)` (from `Over.w` / the slice triangle, via
    `R₀.map_comp`) + `PresheafOfModules.naturality_apply` + `PresheafOfModules.map_smul`. The Module
    axioms close by `PresheafOfModules.hom_ext`+`ModuleCat.hom_ext`+`LinearMap.ext` then `show` to the
    defeq reduced (`appAt`) form + ring-hom lemmas. **Coercion notes for the next builder:** use
    `ModuleCat.comp_apply` (coe, keeps `restrict` intact) NOT `hom_comp`; `erw` the `ofHom`/`appAt`
    reductions (`ConcreteCategory.hom (ModuleCat.ofHom _)` is defeq- but not simp-reducible because
    `ModuleCat.ofHom ≠ ConcreteCategory.ofHom` syntactically); `ModuleCat.restrictScalars.map_apply`.
  - **✅ RESTRICTION MAP DONE (2026-06-14, `main` @ `4e5b000`, full build 8341 jobs, vacuity 0, axioms
    clean): the carrier diamond is CRACKED.** `internalHomMapHom f : internalHomObj X ⟶
    restrictScalars (R₀.map f) (internalHomObj Y)` — the `R₀(X)`-linear (`R₀.map f`-semilinear) map
    underlying `[F,H].map f`.
    - **(✅ `rfl`) the restriction is FREE from `pushforward₀` functoriality:** `internalHomMap f φ :=
      (pushforward₀ (Over.map f.unop) _).map φ` typechecks as `(restrict Y).obj F ⟶ (restrict Y).obj H`
      because `(pushforward₀ (Over.map f.unop) _).obj ((restrict X).obj F) = (restrict Y).obj F` **by
      `rfl`**, and `.app V = φ.app (op ((Over.map f.unop).obj V.unop))` by `rfl`. **So naturality AND
      additivity come free** (it is a functor's `.map`).
    - **(✅ proven) semilinearity** via the same scalar-compat as the object (`R₀((mapObj V).hom.op)(a)
      = R₀(V.hom.op)(R₀.map f a)`, from `(mapObj V).hom = V.hom ≫ f.unop` + `R₀.map_comp`).
    - **🔓 THE CARRIER DIAMOND — RESOLVED TWO WAYS AT ONCE.** The PMod `map` field's `restrictScalars`
      is over the **RingCat** presheaf `R₀⋙forget₂`, but `internalHomObj` lives over the **CommRingCat**
      carrier `R₀.obj X`; the boundary broke synthesis (both carrier choices hit a different
      diamond — see git history of this doc for the dead refactor). FIX:
      (i) **`ModuleCat.semilinearMapAddEquiv (R₀.map f).hom M N`** turns a `→ₛₗ[(R₀.map f).hom]`
          semilinear map into the morphism `M ⟶ (restrictScalars …).obj N` — sidesteps the
          carrier-collapse synthesis failure that direct `ModuleCat.ofHom` of a `→ₗ` into
          `↑(restrictScalars … (internalHomObj Y))` hit (its carrier collapses to `↑(internalHomObj Y)`,
          so synth finds the R₀(Y)-module instead of the restrictScalars R₀(X)-module).
      (ii) write `restrictScalars` over **`(R₀.map f).hom`** (the CommRingCat hom, *reduced* carrier) —
          **defeq** to `((R₀⋙forget₂).map f).hom` (so `internalHomMapHom` still matches the PMod field
          type), but keeps the reduced `↑(R₀.obj X)` carrier where the committed instances register.
          (Root cause: instances register with the reduced carrier `↑(R₀.obj X)`; `(R₀⋙forget₂)`-based
          queries keep the unreduced `↑((R₀⋙forget₂).obj X)` and miss them.)
    - **(⚠ universe) the `[F,H]` presheaf lives in `PresheafOfModules.{max u u' v'}`** (the value is a
      Hom-SET over the slice `Over X.unop`, object universe `max u' v'`); collapses to `.{u}` when
      `u' ≤ u, v' ≤ u` (the single-universe application the port needs).
    - **NEXT — assemble `internalHom : PresheafOfModules.{max u u' v'} R₀'`** with `obj X :=
      internalHomObj`, `map f := internalHomMapHom f`, and the two remaining coherences:
      `map_id` / `map_comp` = the `restrictScalarsId'` / `restrictScalarsComp'` coherences via
      `Over.mapId_eq` / `Over.mapComp_eq` naturality, mirroring `presheafHom`'s `map_id`/`map_comp`
      (`simpa [Over.mapId] using φ.naturality ((Over.mapId X).hom.app Y).op`). **The fiddly bit found
      2026-06-14:** the inner `φ.app A = φ.app B` is a *dependent* app so plain `rw [object_eq]` fails
      ("motive not type correct"); use the `φ.naturality`-across-the-iso route (presheafHom pattern),
      not object-equality rewriting. After that it is a `PresheafOfModules`.
    - then (b) tensor-hom adjunction (`Closed F`). Both then feed piece (III) + the port.
- **Port — `(sheafificationW J R₀).IsMonoidal`.** `whiskerLeft` (`W g ⟹ W (F ◁ g)`): convert
  `Hom(F⊗G_i, F.obj H) ≅ Hom(G_i, [F, F.obj H])` (closed, II), use `[F, F.obj H]` local (III) +
  `sheafificationW.bijective_precomp` (I). `whiskerRight` via the existing
  `PresheafOfModules.symmetricCategory` braiding (cf. `Sites/Monoidal.lean:144`). Assemble
  `IsMonoidal` (`IsMonoidal.mk'`), then drop the `[…IsMonoidal]` hypothesis from
  `SheafOfModules.monoidalCategory` → I.1 unconditional → unblocks I.2.
