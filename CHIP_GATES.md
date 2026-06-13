# Chip gates — jacobian-alggeo-challenge (load before ANY new Lean work)

Ported from jacobian-lean-challenge `tools/chip-prompt-preamble.md` (the 7
anti-paraphrase gates, added 2026-05-23 after that repo ballooned ~130k →
183k+ LOC via paraphrase chips — ~110k LOC of it was later deleted as dead
bloat) and from the sqg-lean-proofs circular-chain post-mortem. This repo
applies them FROM DAY ONE: the goal is a tree that is clean by construction,
not cleaned up after.

Before writing ANY new code, a chip must pass ALL gates. Failing any ⇒
REJECT with `✗ REJECTED` + the failing gate.

## Gate V — vacuity lint (mechanical)

```
python3 "/Volumes/4TB SD/ClaudeCode/noethersolve/scripts/lean_vacuity_lint.py" \
  "/Volumes/4TB SD/ClaudeCode/jacobian-alggeo-challenge" --no-color --max-findings 0
```

**Baseline = 0 (scaffold, 2026-06-13). It stays 0.** Deliberate exceptions
get an inline `-- vacuity-ok: <reason>` waiver named in the chip report.
Rules: `True`-typed fields; `Prop := True`; `True.intro`; structures that
cannot constrain their subject; subject-free hypothesis structures; theorems
with `_`-unused named hypotheses. The linter cannot catch circularity or
misformalization — those stay on the review path (and the comparator pins
the 9 hole statements).

## Gates 1–7 (anti-paraphrase)

1. **Paraphrase gate.** Re-deriving `T_new (h₁…hₖ)` from `T_old (h₁…hₙ)`,
   `k < n`, by naming dropped hypotheses into a NEW structure/class/Prop is
   a renamed sorry. REJECT unless the chip also discharges a named
   hypothesis by classical proof on arbitrary data.
2. **Parallel-route gate.** A second route to an in-tree conclusion is net
   negative. REJECT unless it closes something the existing route does not,
   documented precisely.
3. **Named-hypothesis gate.** A new `class`/`structure`/`def Prop` whose
   discharge is "left as future work" is a renamed sorry. REJECT unless the
   same session discharges it on arbitrary data. NO axioms in this repo,
   named or otherwise — the eval comparator runs `#print axioms`-class
   checks and the bar is sorry-free AND axiom-free.
4. **Per-instance gate.** Concrete-instance smoke tests (e.g. ℙ¹, an
   elliptic curve): at most ONE per session, only if a same-session theorem
   consumes it.
5. **Minimum substantive content.** A chip's `proven:` field must be a
   substantive classical statement in plain math — never "bridges A to B" /
   "packages X into Y" / "reduces N inputs to N−1".
6. **mathlib-first gate.** Grep the pinned mathlib before writing
   infrastructure; if a lemma is within ~50 LOC of glue, use it. New
   infrastructure beyond that gets its own milestone in `OPEN.md`, not a
   silent inline pile (it is also mathlib-PR material — keep it PR-shaped).
7. **Hole-progress gate.** Every chip must either (a) fill one of the 9
   holes in `Challenge.lean` sorry-free, (b) discharge a declared milestone
   from the route doc on arbitrary data, or (c) prove a substantive
   classical lemma a declared milestone consumes. Anything else is REJECT.

## Discipline rules

See `DEVELOPMENT.md` (panic-safe builds, merge gate, ω-binder ban, eval
mechanics). Required chip-report format: `✓ DONE` / `✗ STUCK` with branch,
HEAD, local-verify or CI status, file, `proven:`, `residuals:` — exactly as
in the jacobian preamble.
