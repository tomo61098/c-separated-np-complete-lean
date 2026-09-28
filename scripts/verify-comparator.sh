#!/usr/bin/env bash
set -euo pipefail

# Fetch only this project's Mathlib imports below.
export MATHLIB_NO_CACHE_ON_UPDATE=1

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap git lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

# Lean 4.35.0-rc2 bundles the comparator, exporter, and replay kernels.
# Their versions are selected together by the project's lean-toolchain.
toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar supplies both bundled independent kernels itself. Keep this generated
# configuration out of comparator.json, where external_kernels is forbidden.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

# With no module arguments, Mathlib downloads its entire library. Collect this
# project's direct Mathlib imports; cache get includes their transitive imports.
python3 - "$repository_root" <<'PY'
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
sources = [root / name for name in ("Challenge.lean", "Solution.lean", "CSeparatedNPComplete.lean")]
sources.extend(sorted((root / "CSeparatedNPComplete").rglob("*.lean")))
modules = sorted({
    match.group(1)
    for source in sources
    for match in re.finditer(
        r"^(?:public\s+)?(?:meta\s+)?import\s+(Mathlib(?:\.[A-Za-z0-9_']+)*)\s*$",
        source.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
})
if not modules:
    raise SystemExit("error: no Mathlib imports found; refusing a full-library cache download")
print(f"Fetching cache for {len(modules)} Mathlib imports and their dependencies", flush=True)
subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=root, check=True)
PY
lake comparator --config "$config"
