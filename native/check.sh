#!/bin/bash
# Verifies native (Mathlib-free) modules with the pinned toolchain.
# Fails on: any Mathlib/Batteries import, sorry/admit/axiom/native_decide, or a Lean error.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
files=$(find NativeKernel -name '*.lean' | sort)
if grep -rnE '^\s*import\s+(Mathlib|Batteries|Aesop|Qq|ProofWidgets)' NativeKernel; then
  echo "FAIL: non-core import in native/" >&2; exit 1
fi
if grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\s' NativeKernel; then
  echo "FAIL: forbidden token in native/" >&2; exit 1
fi
for f in $files; do
  lean "$f" > "${TMPDIR:-/tmp}/native_check_out.txt" 2>&1 || { cat "${TMPDIR:-/tmp}/native_check_out.txt" >&2; echo "FAIL: $f" >&2; exit 1; }
  if grep -q 'depends on' "${TMPDIR:-/tmp}/native_check_out.txt" && ! grep -q 'does not depend on any axioms' "${TMPDIR:-/tmp}/native_check_out.txt"; then
    echo "NOTE: $f reports axioms:"; cat "${TMPDIR:-/tmp}/native_check_out.txt"
  fi
  echo "OK: $f"
done
