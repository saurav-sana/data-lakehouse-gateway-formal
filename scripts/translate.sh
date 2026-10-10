#!/usr/bin/env bash
# Translate the PlusCal algorithm into TLA+ (rewrites the .tla in place; keeps a .old backup).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JAR="${TLA_JAR:-$ROOT/tools/tla2tools.jar}"
cd "$ROOT/spec"
java -cp "$JAR" pcal.trans -nocfg DataLakehouseGateway.tla
