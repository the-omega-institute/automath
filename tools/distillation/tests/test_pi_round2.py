import importlib.util
import subprocess
import sys
from pathlib import Path


PIPELINE_PATH = (
    Path(__file__).resolve().parents[2]
    / "chatgpt-oracle"
    / "oracle_pipeline.py"
)


def load_oracle_pipeline():
    spec = importlib.util.spec_from_file_location(
        "oracle_pipeline_pi_round2", PIPELINE_PATH
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


oracle_pipeline = load_oracle_pipeline()


def run_git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )


def init_repo(repo: Path) -> None:
    run_git(repo, "init")
    run_git(repo, "config", "user.email", "pi-round2@example.com")
    run_git(repo, "config", "user.name", "PI Round 2")


def commit_all(repo: Path, message: str) -> str:
    run_git(repo, "add", ".")
    run_git(repo, "commit", "-m", message)
    return run_git(repo, "rev-parse", "HEAD").stdout.strip()


def test_verify_fix_diff_scope_missed_label(tmp_path):
    init_repo(tmp_path)
    paper = tmp_path / "paper"
    paper.mkdir()
    (paper / "main.tex").write_text(
        "\\begin{theorem}\\label{thm:3.2}Important theorem.\\end{theorem}\n",
        encoding="utf-8",
    )
    (paper / "other.tex").write_text("Unrelated text.\n", encoding="utf-8")
    commit_all(tmp_path, "initial")

    (paper / "other.tex").write_text("Unrelated text changed.\n", encoding="utf-8")
    fix_hash = commit_all(tmp_path, "unrelated fix")

    result = oracle_pipeline._verify_fix_diff_scope(
        object(), ["Theorem 3.2 has a gap"], fix_hash, paper
    )

    assert result["all_locations_touched"] is False
    assert "theorem 3.2" in result["missed_locations"]
    assert result["covered_locations"] == []


def test_verify_fix_diff_scope_drift_signal(tmp_path):
    init_repo(tmp_path)
    paper = tmp_path / "paper"
    paper.mkdir()
    (paper / "main.tex").write_text(
        "\\begin{theorem}\\label{thm:3.2}Important theorem.\\end{theorem}\n",
        encoding="utf-8",
    )
    commit_all(tmp_path, "initial")

    added = "\n".join(f"line {idx}" for idx in range(205))
    (paper / "main.tex").write_text(
        "\\begin{theorem}\\label{thm:3.2}Important theorem.\\end{theorem}\n"
        + added
        + "\n",
        encoding="utf-8",
    )
    fix_hash = commit_all(tmp_path, "large fix")

    result = oracle_pipeline._verify_fix_diff_scope(
        object(), ["Theorem 3.2 needs details"], fix_hash, paper
    )

    assert result["diff_size_lines"] > 200
    assert result["drift_signal"] is True


def test_classify_stage_a_failure_infra_fail():
    state = oracle_pipeline.PaperState(
        paper_dir="paper", paper_name="paper", target_journal="journal"
    )
    audit_result = {"metrics": {}, "final_score": None, "issues": []}

    assert oracle_pipeline._classify_stage_a_failure(state, audit_result) == "infra_fail"


def test_classify_stage_a_failure_real_block():
    state = oracle_pipeline.PaperState(
        paper_dir="paper", paper_name="paper", target_journal="journal"
    )
    audit_result = {
        "metrics": {
            "scope_coverage": 3,
            "theorem_completeness": 3,
            "proof_integrity": 3,
            "depth_novelty": 3,
            "journal_fit": 3,
            "split_hygiene": 3,
        },
        "final_score": 3,
        "issues": [
            {"category": "scope"},
            {"category": "proof"},
            {"category": "novelty"},
            {"category": "fit"},
        ],
    }

    assert oracle_pipeline._classify_stage_a_failure(state, audit_result) == "real_block"


def test_classify_stage_a_failure_work_pending():
    state = oracle_pipeline.PaperState(
        paper_dir="paper", paper_name="paper", target_journal="journal"
    )
    threshold = min(oracle_pipeline.STAGE_A_METRIC_THRESHOLDS.values())
    score = threshold - 1
    audit_result = {
        "metrics": {
            "scope_coverage": score,
            "theorem_completeness": score,
            "proof_integrity": score,
            "depth_novelty": score,
            "journal_fit": score,
            "split_hygiene": score,
        },
        "final_score": score,
        "work_packages": [{"task": "tighten proof"}],
        "issues": [],
    }

    assert oracle_pipeline._classify_stage_a_failure(state, audit_result) == "work_pending"


def test_stage_b_fresh_eval_infra_fail(monkeypatch):
    state = oracle_pipeline.PaperState(
        paper_dir="paper", paper_name="paper", target_journal="journal"
    )

    monkeypatch.setattr(oracle_pipeline, "save_state", lambda _state: None)
    monkeypatch.setattr(oracle_pipeline, "oracle_submit", lambda *args, **kwargs: False)

    assert oracle_pipeline._stage_b_fresh_eval(
        state,
        rnd=1,
        oracle_timeout=1,
        dry_run=False,
        tag="[paper|B]",
        safe_name="paper",
    ) == (False, "infra_fail", "")
