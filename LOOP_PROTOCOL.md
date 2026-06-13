# LOOP_PROTOCOL — autonomous fresh-context iterations

Each loop run is a NEW session with no memory of previous runs. **The repo is
the only state.** This file is the authoritative per-run procedure; the
scheduled routine's prompt just points here.

## Per-run procedure (exactly one iteration)

1. **Halt check.** If a file named `LOOP_HALT` exists at the repo root, do
   nothing and exit immediately (report its contents).
2. **Load state, don't re-plan.** Read, in order: `NEXT_SESSION.md`
   (names the current chip + DONE WHEN) → `OPEN.md` (authoritative status)
   → `CHIP_GATES.md` → `DEVELOPMENT.md` → tail of `LOOP_LOG.md`. Do NOT
   audit, re-architect, or re-derive the route; the route doc is
   `docs/ROUTE_RESEARCH_2026_06_13.md` and changes to it must be priced
   against the current milestone's DONE WHEN.
3. **Environment.** Toolchain per `lean-toolchain` (elan). In a CLOUD
   sandbox `lake exe cache get` IS allowed (the ban in DEVELOPMENT.md is
   machine-specific to the local M3 Ultra). On the local machine, follow
   DEVELOPMENT.md throttling rules instead.
4. **Execute exactly ONE chip** toward the current milestone, passing ALL
   gates in `CHIP_GATES.md`. Never modify `Challenge.lean`. No `sorry`, no
   `axiom`, no `ω` binders.
5. **LOC ceiling.** If the run's cumulative diff approaches **3k LOC** (hard
   stop 5k), land what is green, update the handoff, and exit — the next
   run continues fresh. Never push past the ceiling "to finish the thought".
6. **Verify before merge.** `lake build` green in the sandbox AND
   `python3 scripts/lean_vacuity_lint.py . --no-color --max-findings 0`
   PASS. Push the chip on a branch `loop/<yyyymmdd-hhmm>-<slug>`, wait for
   Lean Action CI green, then merge to `main` and push. CI red ⇒ fix or
   record STUCK; never merge red.
7. **Hand off.** Update `OPEN.md` (status) and `NEXT_SESSION.md` (name the
   NEXT chip with its DONE WHEN), and append ONE line to `LOOP_LOG.md`:
   `| <UTC datetime> | <chip> | DONE/STUCK | <LOC merged> | <one-line note> |`
8. **Stuck-breaker.** If this run ends STUCK on the same target as the
   previous `LOOP_LOG.md` entry (two consecutive STUCKs on one target):
   do not retry a third time. Write the obstruction at maximum resolution
   (exact failing goal, error, what was tried) into
   `docs/OBSTRUCTION_<date>.md`, create `LOOP_HALT` containing a one-line
   reason + pointer, commit and push. A human resumes from there.
9. **Milestone events.** When a milestone's DONE WHEN lands, record its
   actual cost (LOC, wall-clock) in the route doc. When M1 lands, make the
   go/no-go call written in the route doc explicitly in `LOOP_LOG.md` —
   if NO-GO, create `LOOP_HALT` per rule 8.

## Quality bar (why the gates exist)

The diffgeo sibling repo grew 130k → 183k+ LOC via unsupervised paraphrase
chips and was later debloated by 110k LOC. This loop exists to produce a
tree that is clean BY CONSTRUCTION: one gated chip per run, ratcheted lint,
named DONE WHENs, and a stuck-breaker instead of grinding. A run that ships
nothing but an honest STUCK + obstruction doc is a GOOD run.
