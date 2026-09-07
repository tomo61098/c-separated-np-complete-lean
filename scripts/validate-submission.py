#!/usr/bin/env python3
"""Repository preflight using Palomar's pinned metadata validator.

Install the verifier checkout's requirements.txt, then run this script with
--policy-root pointing to that checkout. Comparator is a separate check.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy-root", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(args.policy_root.resolve()))
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verification_errors import VerificationError

    errors = []
    try:
        metadata = load_formalization_metadata(root / "formalization.yaml")
        if metadata["project"]["license"] != "Apache-2.0":
            errors.append("Expected Apache-2.0, matching this repository's LICENSE")
        print("PASS: official Palomar metadata validator")
    except VerificationError as error:
        errors.extend(str(issue) for issue in getattr(error, "issues", (error,)))

    config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
    expected = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": ["CSeparatedNPComplete.partition_gadget_schedule_partition_iff"],
        "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    if config != expected:
        errors.append("comparator.json differs from the reviewed main-theorem configuration")
    challenge = (root / "Challenge.lean").read_bytes()
    if len(challenge) > 32 * 1024 or len(challenge.splitlines()) > 300:
        errors.append("Challenge exceeds Palomar's preferred review size")
    imports = re.findall(r"^import\s+(\S+)", challenge.decode("utf-8"), re.MULTILINE)
    if not imports or any(not item.startswith("Mathlib.") for item in imports):
        errors.append("Challenge must use only direct Mathlib imports")
    if (root / "lakefile.lean").exists():
        errors.append("This project must have only lakefile.toml")
    lakefile = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            errors.append(f"Dependency {package['name']} is not pinned to a Git commit")
        if not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"]):
            errors.append(f"Dependency {package['name']} must have a public GitHub URL")
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    if lakefile["require"][0]["rev"] != mathlib["rev"]:
        errors.append("Mathlib Lakefile and manifest revisions differ")
    paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).decode().split("\0")
    compiled = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
    for name in filter(None, paths):
        if Path(name).suffix in compiled or name.startswith(".lake/"):
            errors.append(f"Build artifact must not be tracked: {name}")
    print(f"Challenge: {len(challenge.splitlines())} lines, {len(challenge)} bytes")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("PASS: repository submission preflight (Comparator replay is separate)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
