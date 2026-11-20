# RH (Alpöge) Blueprint

A reading guide to the Lean 4 formalization that claims a proof of the Riemann Hypothesis and of
GRH for all Dirichlet L-functions, announced 2026-11-20 at <https://alpo.ge/remark.pdf>.
The submission is mirrored unmodified, with a Comparator setup, at
[Deicyde/riemann-hypothesis](https://github.com/Deicyde/riemann-hypothesis).

> **Status: unverified.** At the time of writing, the kernel check (Comparator) of the submission
> has not finished. This repository says nothing about whether the proof is correct. It only maps
> how the proof is put together. The plain-math readings and the "crux" labels are my
> interpretation of the Lean source. They have not been checked against the author's paper.

## Why

The submission is about 175,000 Lean files and 17 million lines, with no comments. Directory names
do not describe what is inside, and the import graph says almost nothing because every file is
imported. A *blueprint* is a human-readable map from the main theorems down to the main ideas. It
is the usual first step toward understanding a proof this size. This is a companion to
[navier-stokes-blueprint](https://github.com/jae-63/navier-stokes-blueprint).

## What's here

| Path | What |
|---|---|
| [`BLUEPRINT.md`](BLUEPRINT.md) | the blueprint: statements in plain math from `Main.lean` down to the analytic engine, crux vs. library, pillars, reading order, limits |
| [`graphs/spine.mmd`](graphs/spine.mmd) | hand-drawn graph of the top layers (classical / likely crux / known theorem) |
| `graphs/pillars.{mmd,dot,svg}` | the major areas of the library, with counts of references between them |
| `graphs/decls-depth4.{dot,svg}` | the 441 declarations within 4 steps of the main theorem |
| `graphs/imports-depth4.{dot,svg}` | the import graph, 4 levels down, grouped by directory |
| `data/summary.json` | the numbers behind the tables |
| `scripts/` | index → trace → graphs pipeline: plain Python over the source text, no Lean needed |

## Findings so far

- **The top is classical.** `Main.lean` → GRH in half-plane form (`allChi`) is about 200 lines of
  functional-equation and Euler-factor arguments on top of Mathlib.
- **GRH comes from three inputs plus an analytic engine:**
  - Galois representations for polarized automorphic representations of GL_n over CM fields,
    proved via a theta lift.
  - Local Langlands for GL_n.
  - `VWin`, a bound on Tate–Shafarevich lengths over special cyclotomic subfields.

  The engine is Landau's argument: a square-root bound on smoothed prime sums, on windows of x,
  rules out zeros right of ½.
- **The likely crux:** the window Chebyshev bound (`windowInequality_of_artinInputs`), `VWin`, and
  the families of auxiliary fields built from theta correspondence and Siegel–Weil (`HypsAlt`).
- **The "literature" theorems are proved, not assumed.** 191 of the 195 `*_of_literature` theorems
  (Hironaka, Siegel–Weil, Fargues, Bhatt–Scholze, …) never use their hypothesis bundle, and that
  bundle is itself filled in with proved theorems.

## Reproducing

See the end of [`BLUEPRINT.md`](BLUEPRINT.md#5-files). Indexing the source takes about a minute.
**Do not run `lake build`** on the submission unless you mean to: it needs about 100 GB and hours.

## License

The analysis, scripts and graphs here are Apache-2.0. The submission they describe belongs to its
author and was published without a license. This repository quotes only declaration names and
short statement excerpts from it, and does not redistribute it.
