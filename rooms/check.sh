#!/bin/sh
# The searcher's only tool. usage: check.sh REGIME NODE FILE
#   REGIME  R1_full | R2_binary | R3_none
#   NODE    a node id from blueprint_nodes.yaml, or FINAL to declare the file final
#   FILE    the searcher's current Lean file (the whole development, one file)
# Copies FILE into the pinned project in the VM as Rooms/Target.lean, compiles it with `lake env lean`, logs the file
# and Lean's complete output under results/<REGIME>/attempts/, and prints to the searcher only what the regime allows:
#   R1_full    Lean's complete output
#   R2_binary  the single word ok or error
#   R3_none    nothing until NODE is FINAL; before that the call is refused and not compiled
# Caps: 12 calls per node (R1, R2). A call past the cap is refused, logged, and not compiled. FINAL is always compiled.
set -u
REGIME=${1:?regime}; NODE=${2:?node}; FILE=${3:?file}
HERE=$(cd "$(dirname "$0")/.." && pwd)
LOG="$HERE/results/$REGIME/attempts"; mkdir -p "$LOG"
N=$(ls "$LOG" | grep -c '\.lean$'); N=$((N+1)); SEQ=$(printf '%04d' "$N")
TS=$(date -u +%FT%TZ)
cp "$FILE" "$LOG/$SEQ.lean"
refuse() { printf '%s\t%s\t%s\t%s\t%s\n' "$SEQ" "$TS" "$NODE" "refused" "$1" >> "$HERE/results/$REGIME/calls.tsv"; echo "refused: $1"; exit 3; }
if [ "$REGIME" = R3_none ] && [ "$NODE" != FINAL ]; then refuse "no checker in this regime until FINAL"; fi
if [ "$NODE" != FINAL ]; then
  USED=$(awk -F'\t' -v n="$NODE" '$3==n && $4!="refused"' "$HERE/results/$REGIME/calls.tsv" 2>/dev/null | wc -l | tr -d ' ')
  [ "$USED" -ge 12 ] && refuse "cap of 12 attempts reached for node $NODE"
fi
limactl copy "$FILE" primegaps:/home/heidibennett.guest/rooms/project/Rooms/Target.lean >/dev/null 2>&1 || { echo "tool error: copy failed" ; exit 4; }
START=$(date +%s)
limactl shell primegaps -- sh -c 'cd ~/rooms/project && PATH=$HOME/.elan/bin:$PATH timeout 600 lake env lean Rooms/Target.lean' > "$LOG/$SEQ.out" 2>&1
RC=$?
SECS=$(( $(date +%s) - START ))
if [ $RC -eq 0 ] && ! grep -q -e 'error' -e "declaration uses 'sorry'" "$LOG/$SEQ.out"; then STATUS=ok; else STATUS=error; fi   # a file with sorry is not ok
[ $RC -eq 124 ] && STATUS=timeout
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$SEQ" "$TS" "$NODE" "$STATUS" "rc=$RC" "secs=$SECS" "bytes=$(wc -c < "$FILE" | tr -d ' ')" >> "$HERE/results/$REGIME/calls.tsv"
case "$REGIME" in
  R1_full|R1_noplan) cat "$LOG/$SEQ.out"; echo "[$STATUS]" ;;   # R1_noplan: full feedback, no blueprint (amendment A5)
  R2_binary) echo "$STATUS" ;;
  R3_none) cat "$LOG/$SEQ.out"; echo "[$STATUS]" ;;   # FINAL only: the one check, shown in full
  *) echo "$STATUS" ;;
esac
[ "$STATUS" = ok ]
