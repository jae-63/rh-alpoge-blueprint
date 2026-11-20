#!/bin/bash
# show.sh DeclName  -> prints the declaration block
# usage: RH_SRC=<rh-alpoge/src> RH_WORK=<dir with decls.tsv> show.sh DeclName...
S=${RH_SRC:-../rh-alpoge/src}
D=${RH_WORK:-$(dirname "$0")}
for n in "$@"; do
awk -F'\t' -v n="$n" '$1==n' $D/decls.tsv | head -3 | while IFS=$'\t' read full kind mod line; do
  f=$S/${mod//.//}.lean
  echo "### $full  [$kind]  $mod:$line"
  awk -v s=$line 'NR>=s { if (NR>s && /^(theorem|lemma|def|abbrev|structure|class|instance|inductive|end|namespace|@\[|private|noncomputable|open|section)/) exit; print; if (NR-s>40) {print "  ..."; exit} }' $f
done
done
