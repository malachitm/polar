import json
import subprocess
import unittest
from pathlib import Path


class FreqHornA3SmokeTest(unittest.TestCase):
    def test_freqhorn_emits_payload_for_a3(self):
        repo_root = Path(__file__).resolve().parents[3]
        binary = repo_root / "build" / "tools" / "deep" / "freqhorn"
        benchmark = repo_root / "pwa-horn-benchmarks" / "possible_features" / "algebraic_numbers" / "a3.smt2"
        payload_path = repo_root / "data.json"

        if not binary.exists():
            raise unittest.SkipTest(f"freqhorn binary not built: {binary}")

        if payload_path.exists():
            payload_path.unlink()

        result = subprocess.run(
            [str(binary), "--phaserr", str(benchmark)],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )

        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        self.assertTrue(payload_path.exists(), "freqhorn did not emit data.json")

        payload = json.loads(payload_path.read_text(encoding="utf-8"))
        self.assertGreater(len(payload.get("aux_roots", [])), 0, payload)
        self.assertGreater(len(payload.get("complex_pairs", [])), 0, payload)
        self.assertTrue(
            any(entry.get("period") == 2 for entry in payload.get("complex_pairs", [])),
            payload.get("complex_pairs", []),
        )

        combined_output = result.stdout + result.stderr
        self.assertNotIn("POLAR subprocess failed", combined_output)
        self.assertNotIn("Failed to parse POLAR output as JSON", combined_output)
        self.assertNotIn("Non-constant exponent reached sympy_to_pysmt", combined_output)
        self.assertNotIn("Non-constant exponent reached sympy_to_pysmt2", combined_output)


if __name__ == "__main__":
    unittest.main()