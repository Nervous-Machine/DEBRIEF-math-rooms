# B8_159none_hold_forced — searcher notes (in progress, blocked)

2026-11-27 17:28:19Z start.

1. Removed the 25 `first | <proof> | sorry` fallbacks from the blind arm's file (kept every proof branch;
   rewrote the header comment so the word sorry no longer appears in prose). Remaining `sorry`: N13
   `core_near_extremal` (allowed open) and N16 `c4_free_indep_power` (forced room, not yet attempted).
   Original blind file saved at
   /private/tmp/claude-501/-Users-heidibennett/5d86e9ef-2972-49cb-ba41-8f96433a6c6d/scratchpad/b8_hold/Erdos159_blind_orig.lean

2. 17:30:30Z first check call (tag N01, whole-file compile) was REFUSED by rooms/check.sh:
   "refused: no checker in this regime until FINAL". The regime name B8_159none_hold_forced matches the
   script's `*none*` case (line 311), which refuses every non-FINAL call before the `*forced*` logic is
   reached. Under this name no forced attempt can ever be made, so FINAL could only be accepted with N10,
   N16, N19 textually closed and zero attempts recorded, i.e. a blind arm, not the arm described in the brief.
   No FINAL has been called. Stopped and reported to the caller instead of altering the tool.
