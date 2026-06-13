# NEXT SESSION — entry protocol

Read in order: `OPEN.md` (authoritative hole status) → `CHIP_GATES.md` →
`DEVELOPMENT.md` → `docs/ROUTE_RESEARCH_2026_06_13.md`. Do not re-audit; the
next chip is named below.

## Current phase: M0 → M1

**M0 DONE WHEN:** CI green on the scaffold + `lake-manifest.json` committed
(download from the first CI run's `lake-manifest` artifact:
`gh run download -n lake-manifest`). Local bootstrap build
(`taskpolicy -b nice -n 19 env PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1 lake build`)
runs in the background for HOURS on first run — start it, don't wait on it;
CI is the gate until the local cache is warm.

**M1 (first real chip): Čech H⁰/H¹ for coherent sheaves on a proper curve,
finite-dimensional.** DONE WHEN: `FiniteDimensional k (H¹ C 𝒪_C)` (in
whatever encoding the chip justifies) compiles sorry-free at the pin.
Before writing it: verify exact theorem numbers in Milne JV / FGA Explained
ch. 9 (links in the route doc) and grep the pinned mathlib source tree
(post-bootstrap) for `Cech`, `IsAffineOpen`, quasi-coherent pushforward
finiteness — the inventory in the route doc was path-level only.

M1 is also the arc's go/no-go probe — record its actual LOC + wall-clock in
the route doc when it lands, and make the go/no-go call explicitly there.

## Arc DONE WHEN

A submission accepted by the lean-eval comparator for
`jacobian_challenge_alggeo` (all 9 holes, sorry-free, axiom-free) and
audited by the maintainer.
