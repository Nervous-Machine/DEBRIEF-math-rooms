#!/bin/sh
# The searcher's only tool. usage: check.sh REGIME NODE FILE
#   REGIME  a name containing full, binary or none (R1_full, R2_binary, R3_none, R1_noplan, B2_A_full, ...)
#   NODE    a node id from blueprint_nodes.yaml, or FINAL to declare the file final
#   FILE    the searcher's current Lean file (the whole development, one file)
# Copies FILE into the pinned project in the VM as Rooms/Target.lean, compiles it with `lake env lean`, logs the file
# and Lean's complete output under results/<REGIME>/attempts/, and prints to the searcher only what the regime allows:
#   R1_full    Lean's complete output
#   R2_binary  the single word ok or error
#   R3_none    nothing until NODE is FINAL; before that the call is refused and not compiled
#   *forced*   (build 4) as *full*, plus the forced-attempt rule below
#   *probe*    (build 6) as *full*, plus the probe-first rule below: no room may be left open untried
# Caps: 12 calls per node (R1, R2), or cap= from results/<REGIME>/forced.conf in *forced* regimes (build 5). A call past the cap is
# refused, logged, and not compiled. FINAL is always compiled.
set -u
REGIME=${1:?regime}; NODE=${2:?node}; FILE=${3:?file}
HERE=$(cd "$(dirname "$0")/.." && pwd)
LOG="$HERE/results/$REGIME/attempts"; mkdir -p "$LOG"
N=$(ls "$LOG" | grep -c '\.lean$'); N=$((N+1)); SEQ=$(printf '%04d' "$N")
TS=$(date -u +%FT%TZ)
cp "$FILE" "$LOG/$SEQ.lean"
refuse() { printf '%s\t%s\t%s\t%s\t%s\n' "$SEQ" "$TS" "$NODE" "refused" "$1" >> "$HERE/results/$REGIME/calls.tsv"; echo "refused: $1"; exit 3; }
case "$REGIME" in *none*) [ "$NODE" != FINAL ] && refuse "no checker in this regime until FINAL" ;; esac
CAP=12
case "$REGIME" in *forced*) FCONF="$HERE/results/$REGIME/forced.conf"; [ -f "$FCONF" ] && C=$(sed -n 's/^cap=//p' "$FCONF") && [ -n "$C" ] && CAP=$C ;; esac   # build 5: per-arm cap
if [ "$NODE" != FINAL ]; then
  USED=$(awk -F'\t' -v n="$NODE" '$3==n && $4!="refused"' "$HERE/results/$REGIME/calls.tsv" 2>/dev/null | wc -l | tr -d ' ')
  [ "$USED" -ge "$CAP" ] && refuse "cap of $CAP attempts reached for node $NODE"
fi
# *forced* regimes (build 4): results/<REGIME>/forced.conf names the forced node (node=, name=, allowed=). A call tagged
# with the forced node is refused unless the file has no sorry outside the allowed rooms (a genuine attempt); a FINAL
# is refused while the forced node has fewer than 12 genuine attempts and the file still has sorry outside them.
case "$REGIME" in *forced*)
  FCONF="$HERE/results/$REGIME/forced.conf"
  [ -f "$FCONF" ] || { echo "tool error: forced.conf missing"; exit 4; }
  FNODE=$(sed -n 's/^node=//p' "$FCONF"); FALLOW=$(sed -n 's/^allowed=//p' "$FCONF")
  if [ "$NODE" = "$FNODE" ]; then
    BAD=$(python3 -I "$HERE/rooms/forced_check.py" "$FILE" "$HERE/$FALLOW") || refuse "not a genuine attempt at $FNODE: sorry in $BAD"
  fi
  if [ "$NODE" = FINAL ]; then
    DONE=$(awk -F'\t' -v n="$FNODE" '$3==n && $4!="refused"' "$HERE/results/$REGIME/calls.tsv" 2>/dev/null | wc -l | tr -d ' ')
    if [ "$DONE" -lt "$CAP" ] && ! python3 -I "$HERE/rooms/forced_check.py" "$FILE" "$HERE/$FALLOW" >/dev/null; then
      refuse "FINAL refused: $FNODE has $DONE of $CAP genuine attempts and the file still has sorry outside the allowed rooms"
    fi
  fi ;;
esac
# *probe* regimes (build 6): results/<REGIME>/probe.conf names the blueprint (nodes=). FINAL is refused while any room other
# than a literature_import is still open (sorry, or not declared) and has received no check call tagged with its id or name.
case "$REGIME" in *probe*)
  PCONF="$HERE/results/$REGIME/probe.conf"
  [ -f "$PCONF" ] || { echo "tool error: probe.conf missing"; exit 4; }
  if [ "$NODE" = FINAL ]; then
    PNODES=$(sed -n 's/^nodes=//p' "$PCONF")
    UNTRIED=$(python3 "$HERE/rooms/probe_check.py" "$FILE" "$HERE/$PNODES" "$HERE/results/$REGIME/calls.tsv") || refuse "FINAL refused by the probe rule: rooms left open without one check call: $UNTRIED"
  fi ;;
esac
limactl copy "$FILE" "primegaps:/home/heidibennett.guest/rooms/project/Rooms/Target_$REGIME.lean" >/dev/null 2>&1 || { echo "tool error: copy failed" ; exit 4; }
START=$(date +%s)
limactl shell primegaps -- sh -c 'cd ~/rooms/project && PATH=$HOME/.elan/bin:$PATH timeout 600 lake env lean Rooms/Target_'"$REGIME"'.lean' > "$LOG/$SEQ.out" 2>&1
RC=$?
SECS=$(( $(date +%s) - START ))
if [ $RC -eq 0 ] && ! grep -q 'error' "$LOG/$SEQ.out"; then
  if grep -q 'declaration uses' "$LOG/$SEQ.out"; then STATUS=sorry; else STATUS=ok; fi   # sorry: compiles, but something is left open
else STATUS=error; fi
[ $RC -eq 124 ] && STATUS=timeout
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$SEQ" "$TS" "$NODE" "$STATUS" "rc=$RC" "secs=$SECS" "bytes=$(wc -c < "$FILE" | tr -d ' ')" >> "$HERE/results/$REGIME/calls.tsv"
case "$REGIME" in
  *full*) cat "$LOG/$SEQ.out"; echo "[$STATUS]" ;;      # full feedback (R1_full, R1_noplan, B2_*_full*)
  *binary*) echo "$STATUS" ;;                             # one word (ok, sorry or error)
  *none*) cat "$LOG/$SEQ.out"; echo "[$STATUS]" ;;      # FINAL only: the one check, shown in full
  *) echo "$STATUS" ;;
esac
[ "$STATUS" = ok ]
