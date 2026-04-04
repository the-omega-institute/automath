"""Autoresearch self-evolution memory.

Tracks successful proofs, failure patterns, and difficulty scores across runs.
The LLM reads this memory at each attempt to learn from past experience.

Inspired by Karpathy's autoresearch results.tsv — the agent gets smarter
every night because it remembers what worked and what didn't.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path


MEMORY_DIR = Path(__file__).resolve().parent / "memory"


@dataclass
class ProofExample:
    label: str
    environment: str
    tex_body: str  # LaTeX input (truncated)
    lean_code: str  # Generated Lean4 output
    target_module: str
    repair_rounds: int
    model: str


@dataclass
class FailureRecord:
    label: str
    error_type: str  # compile_error, trivial_proof, forbidden_tokens, etc.
    error_preview: str
    attempts: int
    model: str


@dataclass
class Memory:
    successes: list[ProofExample] = field(default_factory=list)
    failures: list[FailureRecord] = field(default_factory=list)
    skip_labels: set[str] = field(default_factory=set)
    difficulty: dict[str, float] = field(default_factory=dict)  # label → score 0-1
    stats: dict[str, int] = field(default_factory=lambda: {
        "total_attempted": 0,
        "total_succeeded": 0,
        "total_failed": 0,
        "runs_completed": 0,
    })


def load_memory() -> Memory:
    """Load memory from disk. Creates empty memory if none exists."""
    MEMORY_DIR.mkdir(parents=True, exist_ok=True)
    mem = Memory()

    # Load successes
    success_file = MEMORY_DIR / "successes.jsonl"
    if success_file.exists():
        for line in success_file.read_text().strip().split("\n"):
            if not line.strip():
                continue
            data = json.loads(line)
            mem.successes.append(ProofExample(**data))

    # Load failures
    failure_file = MEMORY_DIR / "failures.jsonl"
    if failure_file.exists():
        for line in failure_file.read_text().strip().split("\n"):
            if not line.strip():
                continue
            data = json.loads(line)
            mem.failures.append(FailureRecord(**data))

    # Load skip list
    skip_file = MEMORY_DIR / "skip.json"
    if skip_file.exists():
        mem.skip_labels = set(json.loads(skip_file.read_text()))

    # Load difficulty scores
    diff_file = MEMORY_DIR / "difficulty.json"
    if diff_file.exists():
        mem.difficulty = json.loads(diff_file.read_text())

    # Load stats
    stats_file = MEMORY_DIR / "stats.json"
    if stats_file.exists():
        mem.stats.update(json.loads(stats_file.read_text()))

    return mem


def save_memory(mem: Memory) -> None:
    """Persist memory to disk."""
    MEMORY_DIR.mkdir(parents=True, exist_ok=True)

    with open(MEMORY_DIR / "successes.jsonl", "w") as f:
        for s in mem.successes:
            f.write(json.dumps(s.__dict__, ensure_ascii=False) + "\n")

    with open(MEMORY_DIR / "failures.jsonl", "w") as f:
        for fr in mem.failures:
            f.write(json.dumps(fr.__dict__, ensure_ascii=False) + "\n")

    with open(MEMORY_DIR / "skip.json", "w") as f:
        json.dump(sorted(mem.skip_labels), f, ensure_ascii=False, indent=2)

    with open(MEMORY_DIR / "difficulty.json", "w") as f:
        json.dump(mem.difficulty, f, ensure_ascii=False, indent=2)

    with open(MEMORY_DIR / "stats.json", "w") as f:
        json.dump(mem.stats, f, indent=2)


def record_success(mem: Memory, target: dict, lean_code: str,
                   repair_rounds: int, model: str) -> None:
    """Record a successful proof."""
    mem.successes.append(ProofExample(
        label=target.get("label", ""),
        environment=target.get("environment", ""),
        tex_body=target.get("body", "")[:500],  # Truncate
        lean_code=lean_code[:2000],  # Truncate
        target_module=target.get("target_module", ""),
        repair_rounds=repair_rounds,
        model=model,
    ))
    mem.stats["total_succeeded"] += 1
    mem.stats["total_attempted"] += 1

    label = target.get("label", "")
    # Update difficulty: success lowers difficulty score
    old = mem.difficulty.get(label, 0.5)
    mem.difficulty[label] = max(0.0, old - 0.2)


def record_failure(mem: Memory, target: dict, error_type: str,
                   error_preview: str, attempts: int, model: str) -> None:
    """Record a failed proof attempt."""
    label = target.get("label", "")
    mem.failures.append(FailureRecord(
        label=label,
        error_type=error_type,
        error_preview=error_preview[:300],
        attempts=attempts,
        model=model,
    ))
    mem.stats["total_failed"] += 1
    mem.stats["total_attempted"] += 1

    # Update difficulty: failure raises difficulty score
    old = mem.difficulty.get(label, 0.5)
    new_score = min(1.0, old + 0.15)
    mem.difficulty[label] = new_score

    # Auto-skip if failed too many times (across runs)
    fail_count = sum(1 for f in mem.failures if f.label == label)
    if fail_count >= 3:
        mem.skip_labels.add(label)


def should_skip(mem: Memory, label: str) -> bool:
    """Check if a target should be skipped based on past failures."""
    return label in mem.skip_labels


def get_few_shot_examples(mem: Memory, target: dict, max_examples: int = 3) -> str:
    """Get relevant successful proof examples for few-shot prompting.

    Prioritizes examples from the same module, then same environment type.
    """
    if not mem.successes:
        return ""

    target_module = target.get("target_module", "")
    target_env = target.get("environment", "")

    # Score and sort examples by relevance
    scored = []
    for ex in mem.successes:
        score = 0
        if ex.target_module == target_module:
            score += 3
        if ex.environment == target_env:
            score += 2
        if ex.repair_rounds == 0:
            score += 1  # Prefer first-try successes
        scored.append((score, ex))

    scored.sort(key=lambda x: -x[0])
    selected = [ex for _, ex in scored[:max_examples]]

    if not selected:
        return ""

    parts = ["## Successful proof examples from past runs:\n"]
    for i, ex in enumerate(selected, 1):
        parts.append(f"### Example {i}: {ex.label} ({ex.environment})")
        parts.append(f"Module: {ex.target_module}")
        parts.append(f"Repair rounds needed: {ex.repair_rounds}")
        parts.append(f"```lean4\n{ex.lean_code}\n```\n")

    return "\n".join(parts)


def get_failure_warnings(mem: Memory, target: dict) -> str:
    """Get warnings about past failures for this target or similar ones."""
    label = target.get("label", "")
    target_module = target.get("target_module", "")

    warnings = []

    # Past failures for this exact target
    target_failures = [f for f in mem.failures if f.label == label]
    if target_failures:
        error_types = Counter(f.error_type for f in target_failures)
        warnings.append(
            f"WARNING: This target has failed {len(target_failures)} time(s) before. "
            f"Error types: {dict(error_types)}. Avoid repeating the same approach."
        )
        # Show the most recent error
        last = target_failures[-1]
        warnings.append(f"Last error: {last.error_preview[:200]}")

    # Common failure patterns in same module
    module_failures = [f for f in mem.failures if f.label.split(":")[0] == label.split(":")[0]]
    if len(module_failures) > 5:
        common_errors = Counter(f.error_type for f in module_failures).most_common(2)
        warnings.append(
            f"Note: This module has {len(module_failures)} past failures. "
            f"Common issues: {common_errors}"
        )

    return "\n".join(warnings) if warnings else ""


def get_memory_summary(mem: Memory) -> str:
    """One-line summary for run start."""
    s = mem.stats
    rate = s["total_succeeded"] / max(s["total_attempted"], 1)
    return (
        f"Memory: {len(mem.successes)} successes, {len(mem.failures)} failures, "
        f"{len(mem.skip_labels)} skipped, {rate:.0%} overall success rate, "
        f"{s.get('runs_completed', 0)} prior runs"
    )
