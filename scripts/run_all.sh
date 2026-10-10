#!/usr/bin/env bash
# Runs every scenario and compares the outcome with what is expected.
# Expected clean: MC, MC_nofaults, MC_flightcache.
# Expected to FAIL: MC_mutant (proves the tenant invariants can detect the bug).
# MC_lowblobs: informational (pool pressure; a liveness failure may be a real finding).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
status=0
run() {
  local cfg="$1" expect="$2"
  "$ROOT/scripts/check.sh" "$cfg" > "$ROOT/build/${cfg%.cfg}.log" 2>&1
  local rc=$?
  local got=pass; [ $rc -ne 0 ] && got=fail
  if [ "$expect" = info ]; then echo "[info] $cfg -> $got"
  elif [ "$got" = "$expect" ]; then echo "[ok]   $cfg -> $got (expected)"
  else echo "[BAD]  $cfg -> $got (expected $expect)"; status=1; fi
}
mkdir -p "$ROOT/build"
run MC_nofaults.cfg    pass
run MC.cfg             pass
run MC_flightcache.cfg pass
run MC_mutant.cfg      fail
run MC_lowblobs.cfg    info
exit $status
