#!/usr/bin/env bash
# OsiUb G1 trust gate (lead-owned). Exit 0 iff every check passes.
#  1. spec lock (`SPEC_LOCK.sha256` on `OsiUb/Spec.lean`);
#  2. vendored Heidary sources (`scripts/VENDOR_SHA256SUMS`);
#  3. static scan (`scripts/scan_forbidden.py` across BOTH `OsiUb` and `SparseStack`, with `OsiUb/Gate.lean` and
#     `SparseStack/Gate/Gate.lean` whitelisted by PINNED SHA-256 hashes);
#  4. elaborated gate (`OsiUb.GateCheck`: cone of all 29 `OsiUb.Headline.*` declarations + every constant of `OsiUb`,
#     `SparseStack`, and `SparseFockFormal`: no `sorryAx`, no `native`, axioms strictly within
#     `{propext, Classical.choice, Quot.sound}`, no project `implemented_by`/`extern`/`unsafe`).
#
# Usage: scripts/gate.sh [--static-only] [PROJECT_ROOT]
set -u
STATIC=0
ROOT_ARG=""
for a in "$@"; do
  case "$a" in
    --static-only) STATIC=1 ;;
    *) ROOT_ARG="$a" ;;
  esac
done
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ -n "$ROOT_ARG" ]; then R="$(cd "$ROOT_ARG" && pwd)" || exit 2; else R="$(cd "$SCRIPT_DIR/.." && pwd)"; fi
cd "$R" || exit 2
echo "== project root: $R"
[ -f OsiUb/Spec.lean ] && [ -f SparseStack/Spec.lean ] || { echo "not an osi_ub_v2 checkout: $R"; exit 2; }
fail=0

echo "== 1. spec lock"
if [ -f SPEC_LOCK.sha256 ]; then
  sha256sum -c SPEC_LOCK.sha256 || fail=1
else
  echo "SPEC_LOCK.sha256 missing (not yet locked)"; fail=1
fi

echo "== 2. vendor manifest"
(cd vendor/heidary_formal && sha256sum --quiet -c ../../scripts/VENDOR_SHA256SUMS) && echo "vendor: OK" || fail=1

echo "== 3. static scan (OsiUb + SparseStack)"
OSIUB_GATE_SHA=054c16e5e2700ecb536b040ad1c2aa81b10666576a0ac0105d31b879267e321d
SSTACK_GATE_SHA=9a5e5d0fc94c87c1978183bf1f79ba184d78ceb6c99f2e5329dceb4383827122
CUR_OSIUB_SHA=$(sha256sum OsiUb/Gate.lean | cut -d' ' -f1)
CUR_SSTACK_SHA=$(sha256sum SparseStack/Gate/Gate.lean | cut -d' ' -f1)
if [ "$CUR_OSIUB_SHA" != "$OSIUB_GATE_SHA" ]; then echo "OsiUb/Gate.lean sha256 $CUR_OSIUB_SHA != pinned $OSIUB_GATE_SHA"; fail=1; fi
if [ "$CUR_SSTACK_SHA" != "$SSTACK_GATE_SHA" ]; then echo "SparseStack/Gate/Gate.lean sha256 $CUR_SSTACK_SHA != pinned $SSTACK_GATE_SHA"; fail=1; fi
python3 scripts/scan_forbidden.py --root . --lib OsiUb --spec OsiUb/Spec.lean --whitelist-sha256 "$OSIUB_GATE_SHA" || fail=1
python3 scripts/scan_forbidden.py --root . --lib SparseStack --spec SparseStack/Spec.lean --whitelist-sha256 "$SSTACK_GATE_SHA" || fail=1

if [ "$STATIC" = 1 ]; then echo "GATE_STATIC: $([ $fail = 0 ] && echo PASS || echo FAIL)"; exit $fail; fi

echo "== 4. elaborated gate (OsiUb.GateCheck)"
rm -f .lake/build/lib/lean/OsiUb/GateCheck.olean .lake/build/lib/lean/OsiUb/GateCheck.trace
out=$(timeout 3600 lake build OsiUb.GateCheck 2>&1)
rc=$?
echo "$out" | grep -E 'OSI_GATE|depends on axioms|error|RESULT:' | head -120
[ $rc = 0 ] || fail=1
echo "$out" | grep -q 'OSI_GATE: OK' || fail=1
echo "$out" | grep -q 'OSI_GATE: FAIL' && fail=1
echo "GATE: $([ $fail = 0 ] && echo PASS || echo FAIL)"
exit $fail
