import importlib.util
import os
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
ORACLE_PIPELINE_PATH = ROOT / "tools" / "chatgpt-oracle" / "oracle_pipeline.py"
PI_REVIEW_PATH = ROOT / "tools" / "chatgpt-oracle" / "pi_review.py"


def _load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_fresh_eval_mode_includes_briefing():
    oracle_pipeline = _load_module(
        ORACLE_PIPELINE_PATH, "oracle_pipeline_fresh_eval_framing"
    )

    prompt = oracle_pipeline.build_oracle_review_prompt(
        "Annals of Pure and Applied Logic", framing_mode="fresh_eval"
    )

    assert prompt.startswith("=== FRESH REVIEW BRIEFING ===")
    assert "=== END FRESH REVIEW BRIEFING ===" in prompt
    assert "new Annals of Pure and Applied Logic referee" in prompt


def test_default_mode_excludes_briefing():
    oracle_pipeline = _load_module(
        ORACLE_PIPELINE_PATH, "oracle_pipeline_default_framing"
    )

    prompt = oracle_pipeline.build_oracle_review_prompt(
        "Annals of Pure and Applied Logic", framing_mode="default"
    )

    assert "=== FRESH REVIEW BRIEFING ===" not in prompt
    assert "=== END FRESH REVIEW BRIEFING ===" not in prompt


def test_sample_recent_oracle_responses_shape(tmp_path, monkeypatch):
    pi_review = _load_module(PI_REVIEW_PATH, "pi_review_fresh_eval_framing")
    done_dir = tmp_path / "oracle" / "done"
    done_dir.mkdir(parents=True)

    files = [
        (
            "review_paper_alpha_B1_fresh1_100.md",
            "Overall verdict: Reject\nalpha newest",
            50,
        ),
        (
            "review_paper_alpha_B2_a1_200.md",
            "Overall verdict: Major revision\nalpha older",
            40,
        ),
        (
            "final_paper_beta_C1_300.md",
            "Overall verdict: Accept\nbeta newest",
            80,
        ),
        (
            "paper_beta_oracle_fresh_cycle1_400.md",
            "no verdict here\nbeta older",
            70,
        ),
        (
            "paper_gamma_oracle_deepen_cycle2_500.md",
            "Overall verdict: Minor revision\ngamma newest",
            90,
        ),
    ]
    for name, body, mtime in files:
        path = done_dir / name
        path.write_text(body, encoding="utf-8")
        os.utime(path, (mtime, mtime))

    monkeypatch.setattr(pi_review, "SCRIPT_DIR", tmp_path)

    sample = pi_review._sample_recent_oracle_responses(
        max_papers=2, max_per_paper=2, max_chars_per_response=30
    )

    assert len(sample) <= 4
    assert len({item["paper"] for item in sample}) == 2
    assert all(
        {"paper", "file_basename", "verdict", "response_excerpt"} <= set(item)
        for item in sample
    )
    assert any(item["verdict"] == "Minor revision" for item in sample)
    assert any(item["verdict"] == "Accept" for item in sample)
    assert all(len(item["response_excerpt"]) <= 44 for item in sample)
