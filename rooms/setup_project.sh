#!/bin/sh
# Create the pinned Lean project for the rooms experiment inside the VM. Idempotent. Logs to ~/rooms/setup.log.
# Mathlib ccbef15ebdb41c2addfac682131f83c75904c3c1 (2026-10-16), Lean v4.35.0: the control proof's pin.
set -eu
SHA=ccbef15ebdb41c2addfac682131f83c75904c3c1
TC=leanprover/lean4:v4.35.0
mkdir -p "$HOME/rooms"; cd "$HOME/rooms"
exec >> setup.log 2>&1
echo "== setup start $(date -u +%FT%TZ)"; df -h / | tail -1
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$TC" || true
if [ ! -d project ]; then
  mkdir project && cd project
  echo "$TC" > lean-toolchain
  cat > lakefile.toml <<TOML
name = "rooms"
defaultTargets = ["Rooms"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "$SHA"

[[lean_lib]]
name = "Rooms"
TOML
  mkdir -p Rooms && printf 'import Mathlib\n' > Rooms.lean
  echo "== lake update $(date -u +%FT%TZ)"; lake update
else
  cd project
fi
echo "== cache get $(date -u +%FT%TZ)"; lake exe cache get
echo "== mathlib rev check"; git -C .lake/packages/mathlib rev-parse HEAD
echo "== smoke: compile 'import Mathlib' $(date -u +%FT%TZ)"
printf 'import Mathlib\n#eval Lean.versionString\n' > Smoke.lean && lake env lean Smoke.lean && rm -f Smoke.lean
echo "== setup done $(date -u +%FT%TZ)"; df -h / | tail -1
