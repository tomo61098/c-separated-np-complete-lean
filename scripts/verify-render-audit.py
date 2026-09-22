#!/usr/bin/env python3
"""Run Palomar's core-notation render audit on an already built Challenge.

Run `lake build Challenge` first. Use the pinned PalomarSubmission checkout
from CI for --policy-root, with its Python dependencies installed. This checks
the audit that precedes HTML rendering; it does not run Verso or Comparator.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy-root", required=True, type=Path)
    parser.add_argument("--output", type=Path, help="write validated audit JSON to this file")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    policy = args.policy_root.resolve()
    audit = policy / "scripts" / "core_notation_audit.lean"
    if not audit.is_file():
        parser.error(
            f"{audit} is missing; --policy-root must point to the PalomarSubmission "
            "renderer checkout pinned in .github/workflows/ci.yml"
        )
    sys.path.insert(0, str(policy))
    try:
        from scripts.render_challenge import validated_audit_declarations
        from scripts.verification_errors import VerificationError
        from scripts.verify_submission import load_comparator_config
    except ImportError as error:
        parser.error(f"cannot load Palomar renderer helpers: {error}; install the policy dependencies")

    try:
        config = load_comparator_config(root / "comparator.json")
        declarations = [
            *(("theorem", name) for name in config["theorem_names"]),
            *(("def", name) for name in config.get("definition_names", [])),
        ]
        result = subprocess.run(
            [
                "lake", "env", "lean", "--run", str(audit), config["challenge_module"],
                *(item for pair in declarations for item in pair),
            ],
            cwd=root, capture_output=True, text=True, encoding="utf-8", check=False,
        )
        if result.stderr:
            print(result.stderr, file=sys.stderr, end="")
        if result.returncode:
            if result.stdout:
                print(result.stdout, file=sys.stderr, end="")
            print(
                "FAIL: Palomar core-notation render audit. See the Lean error above. "
                "If Challenge is missing or stale, run `lake build Challenge` first.",
                file=sys.stderr,
            )
            return 1
        rows = validated_audit_declarations(
            json.loads(result.stdout), [name for _, name in declarations]
        )
        output = json.dumps(rows, ensure_ascii=False, indent=2) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(output, encoding="utf-8")
        else:
            print(output, end="")
        print(f"PASS: Palomar core-notation render audit ({len(rows)} declarations)", file=sys.stderr)
        return 0
    except (OSError, ValueError, VerificationError) as error:
        print(f"FAIL: Palomar core-notation render audit: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
