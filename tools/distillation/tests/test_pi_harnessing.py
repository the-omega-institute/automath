import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace


PIPELINE_PATH = (
    Path(__file__).resolve().parents[2]
    / "chatgpt-oracle"
    / "oracle_pipeline.py"
)


def load_oracle_pipeline():
    spec = importlib.util.spec_from_file_location("oracle_pipeline_pi_harnessing", PIPELINE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


oracle_pipeline = load_oracle_pipeline()


def _state():
    return SimpleNamespace(stage_b_issue_streaks={}, events=[])


def test_parser_accept_none_blockers_suppresses_status_rows():
    response = """
    Verdict: Accept
    Remaining blockers preventing acceptance: None

    | Overall verdict | Accept | BLOCKER | Accept |
    | Severity Action Owner | status | BLOCKER | header |
    """

    issues = oracle_pipeline.parse_oracle_issues_strict(response)

    assert not [i for i in issues if i.get("severity") == "BLOCKER"]


def test_parser_major_revision_synthesizes_blocker_from_same_blockers_paragraph():
    response = """
    Overall verdict: Major revision

    The same mathematical blockers remain; in particular Lemma 7.18 is not
    proven and Theorem 7.20 still has a gap.
    """

    issues = oracle_pipeline.parse_oracle_issues_strict(response)

    assert len(issues) >= 1
    assert issues[0]["severity"] == "BLOCKER"
    assert "7.18" in issues[0]["description"] or "7.20" in issues[0]["description"]


def test_parser_reject_without_headers_synthesizes_catch_all_blocker():
    response = "We reject; the contribution is below scope and not a new general theory."

    issues = oracle_pipeline.parse_oracle_issues_strict(response)

    assert len(issues) == 1
    assert issues[0]["severity"] == "BLOCKER"
    assert "below scope" in issues[0]["description"]


def test_update_b_issue_streaks_detects_repeated_blocker_on_second_round():
    state = _state()
    issue = {
        "section": "Lemma 7.18",
        "description": "not proven",
        "suggested_fix": "supply proof",
    }

    first = oracle_pipeline._update_b_issue_streaks(
        state, "reject", "Overall verdict: Reject", [issue]
    )
    second = oracle_pipeline._update_b_issue_streaks(
        state, "major revision", "Overall verdict: Major revision", [issue]
    )

    assert first is None
    assert second == "B_STUCK_REPEATED_BLOCKER"


def test_update_b_issue_streaks_detects_journal_fit_on_second_round():
    state = _state()
    response = (
        "Overall verdict: Reject. The paper is too specialized and out of "
        "the journal's scope."
    )

    first = oracle_pipeline._update_b_issue_streaks(state, "reject", response, [])
    second = oracle_pipeline._update_b_issue_streaks(state, "reject", response, [])

    assert first is None
    assert second == "B_STUCK_JOURNAL_FIT"


def test_update_b_issue_streaks_accept_resets_technical_streaks():
    state = _state()
    issue = {
        "section": "Theorem 7.20",
        "description": "gap remains",
        "suggested_fix": "close gap",
    }

    assert oracle_pipeline._update_b_issue_streaks(
        state, "reject", "Overall verdict: Reject", [issue]
    ) is None
    assert oracle_pipeline._update_b_issue_streaks(
        state, "accept", "Overall verdict: Accept", []
    ) is None
    assert oracle_pipeline._update_b_issue_streaks(
        state, "reject", "Overall verdict: Reject", [issue]
    ) is None


def test_update_b_issue_streaks_keeps_journal_fit_sticky_across_accept():
    state = _state()
    response = (
        "Overall verdict: Reject. This is a specialized computational note "
        "and not a new general theory."
    )

    assert oracle_pipeline._update_b_issue_streaks(state, "reject", response, []) is None
    assert oracle_pipeline._update_b_issue_streaks(
        state, "accept", "Overall verdict: Accept", []
    ) is None
    assert (
        oracle_pipeline._update_b_issue_streaks(state, "reject", response, [])
        == "B_STUCK_JOURNAL_FIT"
    )
