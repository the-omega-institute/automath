import importlib.util
import sys
from pathlib import Path


PIPELINE_PATH = (
    Path(__file__).resolve().parents[2]
    / "chatgpt-oracle"
    / "oracle_pipeline.py"
)


def load_oracle_pipeline():
    spec = importlib.util.spec_from_file_location("oracle_pipeline_stage_b_gates", PIPELINE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


oracle_pipeline = load_oracle_pipeline()


def test_classify_oracle_reject_identifies_journal_fit_reject():
    response = (
        "Overall verdict: reject. This reads like a specialized computational "
        "note and is out of scope for the journal mandate."
    )

    assert oracle_pipeline._classify_oracle_reject(response) == "fit"


def test_canonical_issue_key_normalizes_equivalent_proposition_locations():
    first = oracle_pipeline._canonical_issue_key("3 | Prop. 4.35 | HIGH | bla")
    second = oracle_pipeline._canonical_issue_key(
        "Proposition 4.35 -- different wording"
    )

    assert first == second
