import json
import subprocess
import unittest
from pathlib import Path


class FreqHornComplexPairPhaseSmokeTest(unittest.TestCase):
    def test_freqhorn_emits_genuine_complex_pair_payload(self):
        repo_root = Path(__file__).resolve().parents[3]
        binary = repo_root / "build" / "tools" / "deep" / "freqhorn"
        benchmark = repo_root / "pwa-horn-benchmarks" / "benchmarks" / "complex_pair_phase.smt2"
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
        pair_entries = payload.get("complex_pairs", [])
        self.assertGreater(len(pair_entries), 0, payload)
        self.assertTrue(
            any(entry.get("period") == 8 and entry.get("mag_poly") == ["-2", "0", "1"] for entry in pair_entries),
            pair_entries,
        )

        combined_output = result.stdout + result.stderr
        self.assertNotIn("POLAR subprocess failed", combined_output)
        self.assertNotIn("Failed to parse POLAR output as JSON", combined_output)
        self.assertNotIn("Segmentation fault", combined_output)


if __name__ == "__main__":
    unittest.main()