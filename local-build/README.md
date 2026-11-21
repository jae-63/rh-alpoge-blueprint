# Local build: the classical layers type-check

The full submission needs about 100 GB and hours of build time. This folder builds only the
**import closure of six top-level modules**: 236 of the submission's files, about 34,000 lines.
The files are unmodified, and the Mathlib pin and Lean options match the original lakefile.
The build ran on a 16 GB Mac (Lean v4.33.1).

## Result

All six targets build with no errors. The only output was linter warnings: unused simp arguments,
unused section variables and deprecations. Every key theorem checked depends only on Lean's
three standard axioms. There is no `sorryAx` and nothing beyond the whitelist.

| Module | Theorems checked (`#print axioms`) | What it says |
|---|---|---|
| `CharacterBoxes.ClaimStrip` | `Claim.strip`, `Claim.zeta` | GRH for Re s > ½ gives the critical-line form and RH for ζ |
| `CharacterBoxes.Imprimitive` | `UpperTheory.Top.imprimitive` | if primitive characters have no zeros, neither does any character |
| `TotientGaloisClasses.Landau` | `landau_entire`, `landau_family`, `zero_free_of_Chebyshev_growth` | if Gm(x) ≤ x^θ for large x, there are no zeros with Re s > θ |
| `TotientGaloisClasses.TopWin` | `zeroFreeOn_of_tiedWin_cyc`, `level_of_tiedWin`, `zeroFreeOn_of_tiedAll` | window Chebyshev bounds combined with Landau give zero-freeness |
| `CharacterBoxes.ExistsPageN` | `exists_pageN` | a 2-power tower level e(x) with the `PageN` property always exists |
| `BehrendSets.FinalE` | `trivStab` | finite g-subgroups of GL_k(E) are trivial when [E:ℚ]·k < g−1 |

The output is in [`axioms.out`](axioms.out). Every line reads
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

## What this does and does not show

- **It shows** that the layers the blueprint calls *classical* ([§3](../BLUEPRINT.md#3-crux-vs-library))
  are proved as stated: the reductions from `Main.lean` and the Landau step.
- **Several of these theorems are implications.** `zero_free_of_Chebyshev_growth` and
  `zeroFreeOn_of_tiedWin_cyc` *assume* the window Chebyshev bound. That bound is the likely crux
  (`windowInequality_of_artinInputs`, `VWin`, `HypsAlt`), and it sits in the part of the tree too
  big to build here. This build says nothing about the crux.
- **This is not an independent kernel check.** `#print axioms` relies on Lean's normal
  elaboration and kernel. It is not a replay by a second checker, as Comparator, nanoda or
  `leanchecker` would do.

## Running it

```sh
RH_SRC=../rh-alpoge/src BUILD_DIR=../rh-alpoge-mini ./local-build/setup.sh
```

- **Network.** The build itself runs under macOS `sandbox-exec` ([`build.sb.in`](build.sb.in)),
  with no network and writes only inside `BUILD_DIR` and temp. The only network step is
  `lake exe cache get` for Mathlib, which runs before the sandboxed build.
- **Disk.** Mathlib takes about 7.5 GB and the build outputs about 1.8 GB.
- **Time.** About 160 s per module, mostly the time to load Mathlib. The machine used here was
  short on memory (swap nearly full from other work), so the whole build took about 5 h with
  two parallel jobs. Each Lean process peaked at about 1.7 GB of memory.
- **Lake config.** [`lakefile.toml`](lakefile.toml) must list every top-level folder that appears
  in the closure (`Development`, `Formalism`, `Lemmata`, `ReciprocityTheory`). Otherwise Lake
  reports `unknown module prefix`.

[`modules.txt`](modules.txt) is the closure, computed from the `import` lines.
