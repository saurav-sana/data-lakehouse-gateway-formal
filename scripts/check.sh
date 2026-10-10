#!/usr/bin/env bash
# Usage: scripts/check.sh [config-file]   (default: MC.cfg, relative to spec/)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JAR="${TLA_JAR:-$ROOT/tools/tla2tools.jar}"
CFG="${1:-MC.cfg}"
mkdir -p "$ROOT/build/states"
cd "$ROOT/spec"
java -cp "$JAR" tlc2.TLC -workers auto -metadir "$ROOT/build/states" -config "$CFG" MC
