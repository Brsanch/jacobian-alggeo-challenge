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
