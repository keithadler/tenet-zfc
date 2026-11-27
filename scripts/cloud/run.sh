#!/bin/bash
# theorem-all over Init on a machine set up by scripts/cloud/setup.sh: one process per chunk, P at a time (each process
# has its own GC; small chunks keep each one's memory bounded), then all three checkers and the totals, in
# /workspace/results.tgz.
# usage: run.sh <P> <chunk size> <budget s> [first last]: one pod's share of the chunks (all of them by default)
set -u
P=${1:-28}; C=${2:-10}; B=${3:-120}; FIRST=${4:-0}; LAST=${5:-}
W=/workspace; source $W/env.sh; cd $W/repo
OUT=$W/out; mkdir -p $OUT
DLL=src/TenetZfc.Cli/bin/Release/net10.0/tenet-zfc.dll
n=$(dotnet $DLL theorem-all $W/init.ndjson $W/mm/setmm/set.mm $OUT --chunk-size $C --chunks 999999 | sed -n 's/.* in \([0-9][0-9]*\) chunks.*/\1/p')
echo "chunks: $n"
one() { k=$1; [ -f "$OUT/$(printf 'chunk-%04d.tsv' $k)" ] && return 0
  for try in 1 2 3; do dotnet $DLL theorem-all $W/init.ndjson $W/mm/setmm/set.mm $OUT --chunk-size $C --chunks $k --budget $B > /dev/null 2>&1
    [ -f "$OUT/$(printf 'chunk-%04d.tsv' $k)" ] && return 0; done; echo "chunk $k gave up"; }
export -f one; export OUT DLL W C B
[ -n "$LAST" ] || LAST=$((n - 1)); [ "$LAST" -lt "$n" ] || LAST=$((n - 1))
seq $FIRST $LAST | xargs -P $P -I{} bash -c 'one {}' 
echo PROVE-DONE
scripts/verify-all -j $P $OUT > $W/verify.log 2>&1
python3 scripts/summarize-all $OUT > $W/summary.txt 2>&1
cd $OUT && tar czf $W/results.tgz *.tsv *.verify *.verify.log verify-all.tsv theorem-all.shape ../summary.txt 2>/dev/null
echo RUN-DONE
