#!/usr/bin/env python3
"""
Vacuity linter for Lean 4 proof repos.

Motivated by the sqg-lean-proofs 2026-05-29 audit (see that repo's OPEN.md
banner): a "zero sorry, zero axiom" tree hid a circular regularity chain
because the load-bearing gaps lived in *satisfiable-by-construction* terms
that the kernel happily accepts. Every rule below is the mechanical signature
of a pattern from that incident:

  V1 true-field          binder or structure field of type exactly `True`
                         (the removed `freeDerivativeAtKappaMax` /
                         `materialSegmentExpansion` / `farFieldBoundary`
                         placeholder fields).
  V2 prop-is-true        `def`/`abbrev` whose body is exactly `True`.
  V3 true-intro          any `True.intro` proof term. A repo with no
                         True-valued obligations should contain zero.
  V4 unused-subject      `structure`/`class` with an underscore-named
                         parameter (`(_θ : ...)`): a hypothesis-about-θ that
                         cannot mention θ (the `HasThermostatBound` pattern).
  V5 unused-hypothesis   `theorem`/`lemma` with an underscore-named explicit
                         binder (`(_hStrain : ...)`): claims to derive its
                         conclusion "from" a hypothesis it never uses — the
                         stated implication is decoration
                         (`MaterialMaxPrinciple.of_HstrainHbdry` pattern).
  V6 subject-free        `structure`/`class` with explicit parameters none of
                         which appear in any field: satisfiability is
                         independent of the subject, so the "hypothesis" is
                         `∃ c, 0 ≤ c`-style ≡ True (the `∃ α⋆ < 1` pattern,
                         caught even when the parameter is not underscored).

These are heuristics, not semantics: they cannot catch circularity (a
hypothesis ≈ the conclusion) or misformalization. They catch the *cheap*
hollow patterns that cost a manual audit to find last time. Waive a
deliberate instance with `-- vacuity-ok` on the flagged line or the line
above; prefer waivers over disabling rules, so every exception is visible
and greppable.

Test discipline follows scripts/eqn_lint.py: every rule ships as a
(clean, minimally-mutated) fixture pair in tests/test_lean_vacuity_lint.py —
a rule is only trusted if it passes the clean file AND catches the mutant.

Run:  python scripts/lean_vacuity_lint.py PATH [PATH ...]
          [--disable RULE]... [--max-findings N]
PATH is a .lean file or a directory (recursed for *.lean; `.lake`, `.git`,
and `lake-packages` trees are pruned — never lint vendored mathlib).
`--max-findings N` turns the gate into a ratchet: exit 0 iff findings ≤ N
(record the repo's audited baseline in its gates doc and never let it grow).
"""

import argparse
import os
import re
import sys

RULES = ("true-field", "prop-is-true", "true-intro", "unused-subject",
         "unused-hypothesis", "subject-free")

PRUNE_DIRS = {".lake", ".git", "lake-packages", "build"}

WAIVER = "vacuity-ok"

GREEN, RED, DIM, OFF = "\033[32m", "\033[31m", "\033[2m", "\033[0m"

DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|scoped|partial|unsafe)\s+)*"
    r"(?P<kind>structure|class|theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[^\s({\[:⦃⟨]+)",
    re.M)

TRUE_FIELD_RE = re.compile(r":\s*True\s*(?=\)|,|\}|⦄|$)", re.M)
PROP_TRUE_RE = re.compile(
    r"\b(?:def|abbrev)\s+(?P<name>\S+)[^\n]*:=\s*True\s*$", re.M)
TRUE_INTRO_RE = re.compile(r"\bTrue\.intro\b")
UNDERSCORE_BINDER_RE = re.compile(r"[({⦃]\s*(?P<name>_[^\s:)}⦄]*)\s*:")
IDENT_RE = re.compile(r"[^\W\d][\w'!?]*", re.U)


def _lineno(text, pos):
    return text.count("\n", 0, pos) + 1


def strip_comments_and_strings(text):
    """Blank out `--` line comments, nested `/- -/` blocks, and "..." string
    literals, preserving every newline so positions/line numbers survive.
    Waiver comments are honored by the caller on the *original* text."""
    out = []
    i, n = 0, len(text)
    depth = 0          # nested block-comment depth
    in_line = False    # inside -- comment
    in_str = False     # inside "..." literal
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
        elif depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(c if c == "\n" else " ")
                i += 1
        elif in_str:
            if two == '\\"' or two == "\\\\":
                out.append("  ")
                i += 2
            elif c == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append(c if c == "\n" else " ")
                i += 1
        else:
            if two == "/-":
                depth = 1
                out.append("  ")
                i += 2
            elif two == "--":
                in_line = True
                out.append("  ")
                i += 2
            elif c == '"':
                in_str = True
                out.append(" ")
                i += 1
            else:
                out.append(c)
                i += 1
    return "".join(out)


def collect_files(paths):
    files, missing = [], []
    for p in paths:
        if os.path.isdir(p):
            for base, dirs, names in os.walk(p):
                dirs[:] = sorted(d for d in dirs if d not in PRUNE_DIRS)
                for fn in sorted(names):
                    if fn.endswith(".lean"):
                        files.append(os.path.join(base, fn))
        elif os.path.isfile(p):
            files.append(p)
        else:
            missing.append(p)
    return sorted(set(files)), missing


def _waived(orig_lines, line):
    """True if the 1-based `line` or the line above carries the waiver tag."""
    for ln in (line, line - 1):
        if 1 <= ln <= len(orig_lines) and WAIVER in orig_lines[ln - 1]:
            return True
    return False


def _decl_blocks(stripped):
    """Yield (kind, name, start, header, body) per top-level-ish declaration.

    header = decl start up to the first `:=` or `where` (signature: binders,
    extends clause, result sort); body = the rest of the block (fields for a
    structure, proof/value otherwise). Blocks end at the next declaration.
    Heuristic line-based parsing — good enough for linting, not elaboration.
    """
    decls = list(DECL_RE.finditer(stripped))
    for idx, m in enumerate(decls):
        end = decls[idx + 1].start() if idx + 1 < len(decls) else len(stripped)
        block = stripped[m.start():end]
        cut = len(block)
        for sep_re in (re.compile(r":="), re.compile(r"\bwhere\b")):
            sm = sep_re.search(block)
            if sm and sm.start() < cut:
                cut = sm.start()
        yield (m.group("kind"), m.group("name"), m.start(),
               block[:cut], block[cut:])


def _explicit_params(header):
    """Names of ( )- and { }-bound parameters in a declaration header.
    Instance binders [ ] are skipped (they rarely name the subject)."""
    params, binder_spans = [], []
    i, n = 0, len(header)
    while i < n:
        c = header[i]
        if c in "({":
            close = ")" if c == "(" else "}"
            depth, j = 1, i + 1
            while j < n and depth:
                if header[j] == c:
                    depth += 1
                elif header[j] == close:
                    depth -= 1
                j += 1
            group = header[i + 1:j - 1]
            binder_spans.append((i, j))
            names = group.split(":", 1)[0]
            params.extend(t for t in names.split() if t and t != ":")
            i = j
        elif c == "[":
            depth, j = 1, i + 1
            while j < n and depth:
                if header[j] == "[":
                    depth += 1
                elif header[j] == "]":
                    depth -= 1
                j += 1
            binder_spans.append((i, j))
            i = j
        else:
            i += 1
    leftover = []
    prev = 0
    for s, e in binder_spans:
        leftover.append(header[prev:s])
        prev = e
    leftover.append(header[prev:])
    return params, " ".join(leftover)


def lint_text(text, path, disabled=()):
    """Lint one file's text. Returns [(rule, path, line, detail)]."""
    findings = []
    orig_lines = text.split("\n")
    stripped = strip_comments_and_strings(text)

    def add(rule, pos, detail):
        line = _lineno(stripped, pos)
        if rule not in disabled and not _waived(orig_lines, line):
            findings.append((rule, path, line, detail))

    for m in TRUE_FIELD_RE.finditer(stripped):
        add("true-field", m.start(), "binder/field of type `True`")
    for m in PROP_TRUE_RE.finditer(stripped):
        add("prop-is-true", m.start(),
            "`%s` is defined as `True`" % m.group("name"))
    for m in TRUE_INTRO_RE.finditer(stripped):
        add("true-intro", m.start(), "`True.intro` proof term")

    for kind, name, start, header, body in _decl_blocks(stripped):
        params, sig_rest = _explicit_params(header)
        if kind in ("structure", "class"):
            for m in UNDERSCORE_BINDER_RE.finditer(header):
                add("unused-subject", start + m.start(),
                    "%s `%s` cannot constrain its parameter `%s`"
                    % (kind, name, m.group("name")))
            real = [p for p in params if not p.startswith("_")]
            if real:
                searchable = set(IDENT_RE.findall(sig_rest + body))
                if not any(p in searchable for p in real):
                    add("subject-free", start,
                        "%s `%s`: no field mentions parameter(s) %s — "
                        "satisfiable independently of its subject"
                        % (kind, name, ", ".join("`%s`" % p for p in real)))
        elif kind in ("theorem", "lemma"):
            for m in UNDERSCORE_BINDER_RE.finditer(header):
                add("unused-hypothesis", start + m.start(),
                    "%s `%s` never uses hypothesis `%s`"
                    % (kind, name, m.group("name")))
    return findings


def lint_paths(paths, disabled=()):
    """Lint .lean files under `paths`.
    Returns (findings, errors, n_files)."""
    files, missing = collect_files(paths)
    errors = ["no such file or directory: %s" % p for p in missing]
    if not files and not errors:
        errors.append("no .lean files found under: %s" % ", ".join(paths))
    findings = []
    for path in files:
        with open(path, encoding="utf-8") as fh:
            findings.extend(lint_text(fh.read(), path, disabled))
    findings.sort(key=lambda f: (f[1], f[2], f[0]))
    return findings, errors, len(files)


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Lint Lean 4 sources for mechanically-detectable vacuity "
                    "(True-valued obligations, subject-free hypothesis "
                    "structures, unused named hypotheses).")
    ap.add_argument("paths", nargs="+", help=".lean file(s) or director(ies)")
    ap.add_argument("--disable", action="append", default=[], metavar="RULE",
                    choices=RULES, help="disable a rule (repeatable); prefer "
                    "`-- vacuity-ok` line waivers, which stay greppable")
    ap.add_argument("--max-findings", type=int, default=0, metavar="N",
                    help="ratchet mode: exit 0 iff findings <= N "
                    "(default 0 = any finding fails)")
    ap.add_argument("--no-color", action="store_true")
    args = ap.parse_args(argv)

    color = sys.stdout.isatty() and not args.no_color
    green, red, dim, off = (GREEN, RED, DIM, OFF) if color else ("",) * 4

    findings, errors, n_files = lint_paths(args.paths, set(args.disable))

    print("vacuity lint: %d .lean file(s) under %s\n"
          % (n_files, ", ".join(args.paths)))
    if findings:
        print("  %-19s%-52s%s" % ("rule", "where", "detail"))
        for rule, path, line, detail in findings:
            print("  %-19s%-52s%s" % (rule, "%s:%d" % (path, line), detail))
        print()
    for e in errors:
        print("  - %s" % e)

    ok = not errors and len(findings) <= args.max_findings
    if ok:
        extra = (" (<= --max-findings %d)" % args.max_findings
                 if findings else "")
        print("%sPASS%s  %d finding(s)%s." % (green, off, len(findings), extra))
        return 0
    print("%sFAIL%s  %d finding(s), %d error(s)."
          % (red, off, len(findings), len(errors)))
    return 1


if __name__ == "__main__":
    sys.exit(main())
