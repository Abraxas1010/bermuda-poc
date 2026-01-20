#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MONO_ROOT="$(cd "$ROOT/../.." && pwd)"
OUT_DIR="$ROOT/circuits/build"

mkdir -p "$OUT_DIR"

circom "$ROOT/circuits/bermudaWithdrawCompliance.circom" \
  --r1cs --wasm --sym \
  -o "$OUT_DIR" \
  -l "$MONO_ROOT/node_modules"

circom "$ROOT/circuits/bermudaNoteDeposit.circom" \
  --r1cs --wasm --sym \
  -o "$OUT_DIR" \
  -l "$MONO_ROOT/node_modules"

echo "[OK] Circuits compiled into $OUT_DIR"
