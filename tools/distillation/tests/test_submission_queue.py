"""Tests for _add_to_submission_queue auto-append behavior."""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
PIPE_PATH = ROOT / "tools" / "chatgpt-oracle" / "oracle_pipeline.py"


BOARD_TEMPLATE = """\
# Program Board

更新日期：2026-05-10

## 手动投稿队列 (2026-05-10 快照)

| 论文 | 目标期刊 | 备注 |
|------|---------|------|
| `existing_paper_x` | ETDS | already there |

## 全量状态表

| 目录 | 目标期刊 | 状态 | 改投记录 |
|------|---------|------|---------|
| `existing_paper_x` | ETDS | C-DONE | — |
| `new_paper_y` | JFA | C-7 | — |

## Pipeline 阶段说明
"""


@pytest.fixture
def pipe(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location("opipe_under_test", PIPE_PATH)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["opipe_under_test"] = mod
    spec.loader.exec_module(mod)
    board = tmp_path / "PROGRAM_BOARD.md"
    board.write_text(BOARD_TEMPLATE, encoding="utf-8")
    monkeypatch.setattr(mod, "PROGRAM_BOARD", board)

    class _NullLock:
        def __enter__(self): return self
        def __exit__(self, *a): return False
    monkeypatch.setattr(mod, "git_repo_lock", lambda: _NullLock())
    monkeypatch.setattr(mod, "_invalidate_board_cache", lambda: None)
    return mod, board


def test_enqueue_new_paper(pipe):
    mod, board = pipe
    mod._add_to_submission_queue("new_paper_y", "JFA", "test note")
    text = board.read_text(encoding="utf-8")
    queue_section = text.split("## 全量状态表")[0]
    assert "`new_paper_y`" in queue_section
    assert "JFA" in queue_section
    assert "test note" in queue_section


def test_enqueue_idempotent(pipe):
    mod, board = pipe
    mod._add_to_submission_queue("existing_paper_x", "ETDS", "should not duplicate")
    text = board.read_text(encoding="utf-8")
    queue_section = text.split("## 全量状态表")[0]
    # Only the original row in the queue; no duplicate appended.
    assert queue_section.count("`existing_paper_x`") == 1
    # The note "should not duplicate" must not appear anywhere.
    assert "should not duplicate" not in text


def test_enqueue_preserves_full_status_table(pipe):
    mod, board = pipe
    mod._add_to_submission_queue("new_paper_y", "JFA", "added")
    text = board.read_text(encoding="utf-8")
    assert "## 全量状态表" in text
    assert "`new_paper_y` | JFA | C-7" in text


def test_enqueue_sanitizes_pipe_in_note(pipe):
    mod, board = pipe
    mod._add_to_submission_queue("new_paper_y", "JFA", "note with | pipe")
    text = board.read_text(encoding="utf-8")
    queue_section = text.split("## 全量状态表")[0]
    assert "note with \\| pipe" in queue_section
