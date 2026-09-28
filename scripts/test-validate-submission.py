#!/usr/bin/env python3
"""Exercise the submission preflight against the pinned official policy."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
POLICY_ROOT = None


class SubmissionPreflightTests(unittest.TestCase):
    def setUp(self):
        cache = ROOT / ".cache"
        cache.mkdir(exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="palomar-preflight-", dir=cache)
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "scripts").mkdir()
        shutil.copy2(ROOT / "scripts/validate-submission.py", self.root / "scripts")
        for name in ("formalization.yaml", "comparator.json"):
            shutil.copy2(ROOT / name, self.root / name)
        self.write("lean-toolchain", "leanprover/lean4:v4.35.0-rc2\n")
        self.write(".gitignore", "/.cache/\n/.lake/\n")
        self.write("Challenge.lean", "module\n\npublic import Mathlib.Data.Real.Basic\n")
        self.write("Solution.lean", "module\n\npublic import Mathlib.Data.Real.Basic\n")
        revision = "0" * 40
        self.write("lakefile.toml", f'[[require]]\nname = "mathlib"\nrev = "{revision}"\n')
        self.write("lake-manifest.json", json.dumps({"packages": [{
            "name": "mathlib", "type": "git", "rev": revision,
            "url": "https://github.com/leanprover-community/mathlib4",
        }]}))
        self.git("init", "--quiet")
        self.git("add", ".")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def git(self, *arguments):
        subprocess.run(["git", *arguments], cwd=self.root, check=True, capture_output=True)

    def preflight(self, expected_status):
        result = subprocess.run(
            [sys.executable, str(self.root / "scripts/validate-submission.py"),
             "--policy-root", str(POLICY_ROOT)],
            cwd=self.root, capture_output=True, text=True, encoding="utf-8", check=False,
        )
        self.assertEqual(result.returncode, expected_status, result.stdout + result.stderr)
        return result

    def test_public_imports_and_supported_toolchains(self):
        for version in ("v4.35.0-rc2", "v4.35.0-rc10", "v4.35.0", "v4.36.0-rc1"):
            with self.subTest(version=version):
                self.write("lean-toolchain", f"leanprover/lean4:{version}\n")
                result = self.preflight(0)
                self.assertIn("PASS: official Palomar metadata validator", result.stdout)

    def test_old_toolchains_fail_even_when_metadata_passes(self):
        for version in ("v4.32.0", "v4.34.0", "v4.35.0-rc1"):
            with self.subTest(version=version):
                self.write("lean-toolchain", f"leanprover/lean4:{version}\n")
                result = self.preflight(1)
                self.assertIn("PASS: official Palomar metadata validator", result.stdout)
                self.assertIn("older than the minimum Palomar supports (v4.35.0-rc2)", result.stderr)

    def test_non_release_toolchain_fails(self):
        self.write("lean-toolchain", "leanprover/lean4:nightly\n")
        self.assertIn("unsupported Lean toolchain", self.preflight(1).stderr)

    def test_missing_challenge_module_header_fails(self):
        self.write("Challenge.lean", "public import Mathlib.Data.Real.Basic\n")
        self.assertIn("Challenge.lean must begin with the module header", self.preflight(1).stderr)

    def test_new_auxiliary_source_also_requires_module_header(self):
        self.write("scripts/NewAudit.lean", "import Lean\n")
        self.assertIn("scripts/NewAudit.lean must begin with the module header", self.preflight(1).stderr)

    def test_header_comments_follow_official_policy(self):
        self.write("Solution.lean", "/- Ordinary /- nested -/ comment -/\nmodule\n")
        self.preflight(0)
        self.write("Solution.lean", "/-! Documentation is a command. -/\nmodule\n")
        self.assertIn("Solution.lean must begin with the module header", self.preflight(1).stderr)

    def test_source_line_limit(self):
        self.write("Solution.lean", "module\n" + "-- line\n" * 10_000)
        self.assertIn("Solution.lean has 10,001 lines", self.preflight(1).stderr)

    def test_public_project_import_is_rejected(self):
        self.write("Challenge.lean", "module\npublic import Mathlib.Data.Real.Basic\npublic import Solution\n")
        self.assertIn("Challenge must use only direct Mathlib imports", self.preflight(1).stderr)

    def test_metadata_requirements_remain_enforced(self):
        metadata = (self.root / "formalization.yaml").read_text(encoding="utf-8")
        self.write("formalization.yaml", metadata.replace('  authors: ["Tomislav Prusina"]\n', "", 1))
        self.assertIn("project.authors", self.preflight(1).stderr)

    def test_module_artifacts_must_not_be_tracked(self):
        for artifact in ("Example.olean.private", "Example.olean.server", "Example.ir"):
            self.write(artifact, "compiled artifact")
            self.git("add", artifact)
        result = self.preflight(1)
        for artifact in ("Example.olean.private", "Example.olean.server", "Example.ir"):
            self.assertIn(f"Build artifact must not be tracked: {artifact}", result.stderr)

    def test_ignored_cache_sources_are_not_submission_sources(self):
        self.write(".cache/legacy-policy/Old.lean", "import Lean\n")
        self.write(".lake/packages/dependency/Old.lean", "import Lean\n")
        self.preflight(0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy-root", required=True, type=Path)
    args, unittest_arguments = parser.parse_known_args()
    POLICY_ROOT = args.policy_root.resolve()
    unittest.main(argv=[sys.argv[0], *unittest_arguments])
