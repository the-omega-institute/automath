import time
import unittest
from pathlib import Path

from tools.distillation import distill


def oracle_body(title: str) -> str:
    long_note = "x" * 1400
    return (
        "ChatGPT said:\n"
        "{\n"
        '  "status": "ok",\n'
        '  "main_theorem_chain": [\n'
        "    {\n"
        '      "type": "theorem",\n'
        f'      "proposed_title": "{title}",\n'
        '      "target_sections": ["folding"],\n'
        '      "omega_objects": ["Fold_m"],\n'
        '      "minimal_hypotheses": ["H"],\n'
        f'      "conclusion": "C {long_note}",\n'
        '      "proof_spine": ["bad example", "skeleton", "budget", "closure"],\n'
        '      "novelty_reason": "project-bound",\n'
        '      "risk_to_avoid": "overclaim"\n'
        "    }\n"
        "  ]\n"
        "}\n"
    )


class OracleRecoveryTests(unittest.TestCase):
    def test_strip_oracle_response_metadata(self):
        text = '<!-- oracle metadata: {"task_id":"x"} -->\n\n{"status":"ok"}'
        self.assertEqual(distill._strip_oracle_response_metadata(text), '{"status":"ok"}')

    def test_recover_skips_newer_invalid_done_file(self):
        state = distill.DistillState("Wang-Zahl")
        state.depth_cycle = 2
        old_done_dir = distill.ORACLE_DONE_DIR
        try:
            with distill._temporary_directory(prefix="oracle_recovery_") as tmp:
                done_dir = Path(tmp)
                distill.ORACLE_DONE_DIR = done_dir
                valid = done_dir / "wang_zahl_W_oracle_deepen_cycle2_20260423_000506.md"
                invalid = done_dir / "wang_zahl_W_oracle_deepen_cycle2_20260423_013203.md"
                valid.write_text(
                    '<!-- oracle metadata: {"task_id":"valid"} -->\n\n'
                    + oracle_body("valid theorem"),
                    encoding="utf-8",
                )
                time.sleep(0.01)
                invalid.write_text(
                    '<!-- oracle metadata: {"task_id":"invalid"} -->\n\n'
                    "Files:\nMarkdown writeback bundle\nRaw TeX bundle\n",
                    encoding="utf-8",
                )

                recovered = distill._recover_oracle_deepening_from_done(state, 2)
        finally:
            distill.ORACLE_DONE_DIR = old_done_dir
        self.assertIsNotNone(recovered)
        data, source_path, response = recovered
        self.assertEqual(source_path.name, valid.name)
        self.assertEqual(data["status"], "ok")
        self.assertEqual(data["main_theorem_chain"][0]["proposed_title"], "valid theorem")
        self.assertIn("valid theorem", response)

    def test_recover_accepts_free_form_theorem_text(self):
        state = distill.DistillState("Wang-Zahl")
        state.depth_cycle = 5
        old_done_dir = distill.ORACLE_DONE_DIR
        theorem_text = (
            "2026-04-23T10:00:00+08:00\n"
            "Theorem. Let the fold-aware carrier system be fixed. "
            "Assume a worst counterexample remains non-sticky at every "
            "coarse scale. Then the carrier budget grows linearly.\n"
            "Proof. The bad example is first localized, then classified into "
            "a non-sticky skeleton, then the budget inequality is iterated. "
            + "This proof sentence is deliberately long. " * 50
        )
        try:
            with distill._temporary_directory(prefix="oracle_recovery_") as tmp:
                done_dir = Path(tmp)
                distill.ORACLE_DONE_DIR = done_dir
                raw = done_dir / "wang_zahl_W_oracle_deepen_cycle5_a1_20260423_100000.md"
                raw.write_text(
                    '<!-- oracle metadata: {"task_id":"raw"} -->\n\n' + theorem_text,
                    encoding="utf-8",
                )

                recovered = distill._recover_oracle_deepening_from_done(state, 5)
        finally:
            distill.ORACLE_DONE_DIR = old_done_dir
        self.assertIsNotNone(recovered)
        data, _, _ = recovered
        self.assertEqual(data["status"], "ok_raw")
        self.assertIn("carrier budget grows linearly", data["raw_research_text"])


class OracleBridgeStatusTests(unittest.TestCase):
    def test_claimed_agent_infos_filters_to_task_id(self):
        status = {
            "agents": {
                "oracle_1": {"task_id": "wanted", "elapsed": 10, "phase": "sent"},
                "oracle_2": {"task_id": "other", "elapsed": 999, "phase": "prompt_ready"},
                "oracle_3": "malformed",
            }
        }

        claimed = distill._oracle_claimed_agent_infos(status, "wanted")

        self.assertEqual(len(claimed), 1)
        self.assertEqual(claimed[0][0], "oracle_1")

    def test_stale_agent_claim_detects_heartbeat_age(self):
        status = {
            "agents": {
                "oracle_1": {"task_id": "task", "elapsed": 299, "phase": "waiting_response"},
                "oracle_2": {"task_id": "task", "elapsed": 300, "phase": "prompt_ready"},
            }
        }

        stale = distill._oracle_stale_agent_claims(status, "task", stale_timeout=300)

        self.assertEqual(len(stale), 1)
        self.assertEqual(stale[0][0], "oracle_2")


if __name__ == "__main__":
    unittest.main()
