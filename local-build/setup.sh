#!/usr/bin/env bash
# Build a small project from 236 modules of the submission and type-check them in a sandbox.
#   RH_SRC     path to the submission's src/ (default ../rh-alpoge/src)
#   BUILD_DIR  where to create the project (default ../rh-alpoge-mini)
# macOS only, because the sandbox is sandbox-exec.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
RH_SRC="${RH_SRC:-$here/../../rh-alpoge/src}"
BUILD_DIR="${BUILD_DIR:-$here/../../rh-alpoge-mini}"
mkdir -p "$BUILD_DIR/src" "$BUILD_DIR/check"
BUILD_DIR="$(cd "$BUILD_DIR" && pwd)"

while read -r m; do
  f="${m//.//}.lean"
  mkdir -p "$BUILD_DIR/src/$(dirname "$f")"
  cp "$RH_SRC/$f" "$BUILD_DIR/src/$f"
done < "$here/modules.txt"

cp "$here/lakefile.toml" "$here/lean-toolchain" "$BUILD_DIR/"
cp "$here/Axioms.lean" "$BUILD_DIR/check/"
sed "s|BUILD_DIR|$BUILD_DIR|" "$here/build.sb.in" > "$BUILD_DIR/build.sb"

cd "$BUILD_DIR"
lake exe cache get          # the only step that uses the network: Mathlib's prebuilt files
LEAN_NUM_THREADS=2 sandbox-exec -f build.sb lake build \
  Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip \
  Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive \
  Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN \
  Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Landau \
  Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin \
  Formalism.BehrendSets.FinalE
sandbox-exec -f build.sb lake env lean check/Axioms.lean
