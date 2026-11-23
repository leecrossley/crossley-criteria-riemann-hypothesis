#!/usr/bin/env bash
# Check the source hashes and the theta-window receipts, rebuild landau/ against the pinned
# Mathlib, replay every module in the kernel checker, and audit the axioms of the two theorems
# that the proof of RH takes from landau/.
set -euo pipefail

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'Use the build steps in README.md on this platform.' >&2
  exit 2
fi

repo=$(cd "$(dirname "$0")" && pwd)

(cd "$repo/landau" && sha256sum --check --quiet SHA256SUMS)
echo "landau sources match SHA256SUMS"
python3 - "$repo/theta-window" <<'PY'
import hashlib, json, sys
d = sys.argv[1]
source = hashlib.sha256(open(f"{d}/ConvertedThetaWindows.lean", "rb").read()).hexdigest()
receipt = json.load(open(f"{d}/verification.json"))
replay = json.load(open(f"{d}/independent-replay.json"))
assert source == receipt["source_sha256"] == replay["source_sha256"], "the source differs from its receipts"
assert receipt["object_sha256"] == replay["object_sha256"], "the receipts record different objects"
for line in receipt["axiom_output"] + replay["axiom_output"]:
    assert line.endswith("depends on axioms: [propext, Classical.choice, Quot.sound]"), line
print("theta-window source matches both receipts, which report the standard axioms only")
PY

scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
cd "$scratch"

download() {
  curl --fail --location --silent --show-error --retry 4 --output "$2" "$1"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check -
}
download https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
  lean.tar.zst 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
tar --zstd -xf lean.tar.zst
rm -- lean.tar.zst
export PATH="$scratch/lean-4.33.1-linux/bin:$PATH"

cp -R "$repo/landau" landau
cd landau
lake exe cache get
lake build

modules=$(cd src && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort)
for module in $modules; do
  lake env leanchecker "$module"
  echo "kernel replay passed: $module"
done

cat > Audit.lean <<'LEAN'
import IndependentLandau.ZetaWindow
import Reflection
#print axioms IndependentLandau.zeta_zeroFree_of_window
#print axioms RiemannReduction.rh_of_right
LEAN
lake env lean Audit.lean > axioms.txt
cat axioms.txt
python3 - axioms.txt <<'PY'
import re, sys
text = " ".join(open(sys.argv[1]).read().split())
for name in ("IndependentLandau.zeta_zeroFree_of_window", "RiemannReduction.rh_of_right"):
    found = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", text)
    assert found and found.group(1) == "propext, Classical.choice, Quot.sound", f"{name}: {found and found.group(1)}"
print("both theorems use the standard axioms only")
PY
echo "verified"
