#!/usr/bin/env bash
# Checks that vendor/BKMPillar is exactly the upstream pillar sources with the documented
# mechanical rename (namespace NavierStokes3D -> FeffermanNavierStokes3D; module prefixes
# FeffermanClayNS / PeriodicNSContinuation -> BKMPillar.FeffermanClayNS / BKMPillar.PeriodicNSContinuation).
#   bash scripts/check_vendor.sh
set -euo pipefail
cd "$(dirname "$0")/.."
FEF_REV=ebcf10921e02350e46b32b3bcded8dd8ca2c87c4
PNC_REV=502ff17
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
git clone -q https://github.com/BenFrohman/fefferman-clay-navier-stokes.git "$tmp/fef"
git -C "$tmp/fef" checkout -q "$FEF_REV"
git clone -q https://github.com/BenFrohman/periodic-ns-classical-continuation.git "$tmp/pnc"
git -C "$tmp/pnc" checkout -q "$PNC_REV"
xform() {
  sed -E 's/\bNavierStokes3D\b/FeffermanNavierStokes3D/g; s/^((public )?import )(FeffermanClayNS|PeriodicNSContinuation)\b/\1BKMPillar.\3/' "$1"
}
fail=0
check() { # upstream vendored
  if ! diff -q <(xform "$1") "$2" >/dev/null; then echo "MISMATCH: $2"; fail=1; fi
}
check "$tmp/fef/FeffermanClayNS.lean" vendor/BKMPillar/FeffermanClayNS.lean
for f in vendor/BKMPillar/FeffermanClayNS/*.lean; do
  check "$tmp/fef/FeffermanClayNS/$(basename "$f")" "$f"
done
for f in vendor/BKMPillar/PeriodicNSContinuation/*.lean; do
  check "$tmp/pnc/PeriodicNSContinuation/$(basename "$f")" "$f"
done
n=$(ls vendor/BKMPillar/FeffermanClayNS/*.lean vendor/BKMPillar/PeriodicNSContinuation/*.lean | wc -l)
if [ "$fail" = 0 ]; then echo "VENDOR OK ($((n + 1)) files = upstream fefferman@$FEF_REV + periodic-ns-classical-continuation@$PNC_REV, renamed)"; else exit 1; fi
