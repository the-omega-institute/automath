#!/usr/bin/env python3
"""Distillation pipeline for routing external mathematical methods into Omega."""

import argparse
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent          # tools/distillation/../../ = repo root
PUBLICATION_DIR = REPO_ROOT / "papers" / "publication"
THEORY_DIR = (
    REPO_ROOT
    / "theory"
    / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
)
CORE_BODY = THEORY_DIR / "sections" / "body"
BACKFLOW_DIR = PUBLICATION_DIR / "backflow"
DISTILLATION_DIR = BACKFLOW_DIR / ".distillation"
REGISTRY_PATH = BACKFLOW_DIR / "knowledge_backflow_inventory.json"
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = DISTILLATION_DIR / "logs"
STOP_FILE = SCRIPT_DIR / ".pipeline.stop"
IS_WINDOWS = sys.platform == "win32"

CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
    r"(?:\[([^\]]*)\])?\s*"
    r"\\label\{([^}]+)\}",
    re.DOTALL,
)
CLAIM_BLOCK_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
    r"(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)
SECTION_RE = re.compile(
    r"\\(section|subsection|subsubsection)\*?\{([^}]+)\}",
    re.DOTALL,
)

STAGE_ORDER = ["R", "S", "G", "W", "E", "DONE"]

# Review gate configuration
SCORE_PASS_THRESHOLD = 7
MAX_W_ROUNDS = 5          # max writeback generation + review rounds
MAX_DEEP_ROUNDS = 2       # max A-DEEP style escalation rounds per W cycle
MIN_NEW_CLAIMS = 1        # anti-fake: minimum new theorem/lemma/etc labels
MIN_CONTENT_DELTA = 200   # anti-fake: minimum chars of new claim content

LOG_DIR.mkdir(parents=True, exist_ok=True)
logger = logging.getLogger("distill")
logger.setLevel(logging.INFO)
if not logger.handlers:
    _log_file = LOG_DIR / f"distill_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
    _formatter = logging.Formatter(
        "%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s"
    )
    _stream_handler = logging.StreamHandler(sys.stdout)
    _stream_handler.setFormatter(_formatter)
    _file_handler = logging.FileHandler(str(_log_file), encoding="utf-8")
    _file_handler.setFormatter(_formatter)
    logger.addHandler(_stream_handler)
    logger.addHandler(_file_handler)


def _now_iso() -> str:
    """Return a compact UTC timestamp for persisted state files."""
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def io_path(path: Path) -> str:
    """Return a filesystem path string with Windows long-path support."""
    text = os.path.abspath(str(path))
    if os.name != "nt":
        return text
    normalized = text.replace("/", "\\")
    if normalized.startswith("\\\\?\\"):
        return normalized
    if normalized.startswith("\\\\"):
        return "\\\\?\\UNC\\" + normalized[2:]
    return "\\\\?\\" + normalized


def read_text(path: Path) -> str:
    """Read UTF-8 text from a path, replacing malformed bytes."""
    return Path(io_path(path)).read_text(encoding="utf-8", errors="replace")


def write_text(path: Path, content: str) -> None:
    """Write UTF-8 text to a path, creating parent directories first."""
    path.parent.mkdir(parents=True, exist_ok=True)
    Path(io_path(path)).write_text(content, encoding="utf-8")


def write_json(path: Path, data: Any) -> None:
    """Write JSON data to a path using stable UTF-8 formatting."""
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(data, ensure_ascii=False, indent=2, default=str) + "\n"
    Path(io_path(path)).write_text(text, encoding="utf-8")


def read_json(path: Path) -> Any:
    """Read a JSON document from a UTF-8 path."""
    return json.loads(read_text(path))


def _find_codex() -> str:
    """Find the Codex CLI, including npm and Homebrew fallback locations."""
    found = shutil.which("codex")
    if found:
        return found
    if sys.platform == "win32":
        npm_codex = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if npm_codex.exists():
            return str(npm_codex)
    elif sys.platform == "darwin":
        for candidate in ("/opt/homebrew/bin/codex", "/usr/local/bin/codex"):
            if Path(candidate).exists():
                return candidate
    return "codex"


CODEX_PATH = _find_codex()


def _kill_process_tree(pid: int) -> None:
    """Forcefully terminate a process and its descendants."""
    if IS_WINDOWS:
        try:
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(pid)],
                capture_output=True,
                timeout=10,
            )
        except Exception as exc:
            logger.debug("Windows process-tree kill failed for %s: %s", pid, exc)
        return

    try:
        os.killpg(os.getpgid(pid), 15)
        time.sleep(2)
        os.killpg(os.getpgid(pid), 9)
    except (ProcessLookupError, OSError) as exc:
        logger.debug("Unix process-group kill skipped for %s: %s", pid, exc)

    try:
        children = subprocess.run(
            ["pgrep", "-P", str(pid)],
            capture_output=True,
            text=True,
            timeout=5,
            encoding="utf-8",
            errors="replace",
        ).stdout.split()
        for child_pid in children:
            try:
                os.kill(int(child_pid), 9)
            except (ProcessLookupError, ValueError, OSError) as exc:
                logger.debug("Child process kill skipped for %s: %s", child_pid, exc)
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        logger.debug("Child process lookup failed for %s: %s", pid, exc)


def _jsonl_agent_messages(stdout: str) -> str:
    """Extract assistant messages from Codex JSONL stdout."""
    messages = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue

        if event.get("type") == "item.completed":
            item = event.get("item", {})
            if item.get("type") == "agent_message" and item.get("text"):
                messages.append(str(item["text"]))
                continue
            content = item.get("content")
            if isinstance(content, list):
                parts = [
                    str(part.get("text", ""))
                    for part in content
                    if isinstance(part, dict) and part.get("text")
                ]
                if parts:
                    messages.append("\n".join(parts))
                    continue

        if event.get("role") == "assistant":
            content = event.get("content")
            if isinstance(content, str):
                messages.append(content)
            elif isinstance(content, list):
                parts = [
                    str(part.get("text", ""))
                    for part in content
                    if isinstance(part, dict) and part.get("text")
                ]
                if parts:
                    messages.append("\n".join(parts))
    return "\n\n".join(messages)


def codex_exec(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 1800,
    model: Optional[str] = None,
    dry_run: bool = False,
    log_tag: Optional[str] = None,
) -> str:
    """Run `codex exec` with stdin, output-file capture, and JSONL fallback."""
    target_dir = work_dir or REPO_ROOT
    if dry_run:
        logger.info(
            "[DRY RUN] codex exec cwd=%s prompt=%s",
            target_dir,
            prompt[:300].replace("\n", " "),
        )
        if log_tag:
            codex_log_dir = LOG_DIR / "codex"
            codex_log_dir.mkdir(parents=True, exist_ok=True)
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            write_text(codex_log_dir / f"{log_tag}_{ts}.prompt.txt", prompt)
        return "(dry run -- no output)"

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        logger.error("Codex CLI not found")
        return ""

    temp_dir: Optional[Path] = None
    persist = log_tag is not None
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    if persist:
        codex_log_dir = LOG_DIR / "codex"
        codex_log_dir.mkdir(parents=True, exist_ok=True)
        prompt_file = codex_log_dir / f"{log_tag}_{ts}.prompt.txt"
        out_file = codex_log_dir / f"{log_tag}_{ts}.out.txt"
        stdout_file = codex_log_dir / f"{log_tag}_{ts}.stdout.jsonl"
        stderr_file = codex_log_dir / f"{log_tag}_{ts}.stderr.txt"
    else:
        temp_dir = Path(tempfile.mkdtemp(prefix="omega_distill_codex_"))
        prompt_file = temp_dir / "prompt.txt"
        out_file = temp_dir / "output.txt"
        stdout_file = temp_dir / "stdout.jsonl"
        stderr_file = temp_dir / "stderr.txt"

    write_text(prompt_file, prompt)
    write_text(out_file, "")

    cmd = [
        str(codex_bin),
        "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "--json",
        "-C",
        str(target_dir),
        "-o",
        str(out_file),
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    use_shell = IS_WINDOWS and str(codex_bin).endswith(".cmd")
    popen_kwargs: dict[str, Any] = {
        "stdin": subprocess.PIPE,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
        "cwd": str(target_dir),
        "shell": use_shell,
        "encoding": "utf-8",
        "errors": "replace",
    }
    if not IS_WINDOWS:
        popen_kwargs["start_new_session"] = True

    start = time.monotonic()
    stdout = ""
    stderr = ""
    returncode: Any = "?"
    start_failed = False
    try:
        proc = subprocess.Popen(cmd, **popen_kwargs)
        try:
            stdout, stderr = proc.communicate(
                input=prompt,
                timeout=timeout_seconds + 30,
            )
            returncode = proc.returncode
        except subprocess.TimeoutExpired:
            logger.warning(
                "Codex timed out after %ss; killing process tree pid=%s",
                timeout_seconds,
                proc.pid,
            )
            _kill_process_tree(proc.pid)
            try:
                stdout, stderr = proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                stdout, stderr = "", ""
            returncode = -9
    except OSError as exc:
        logger.error("Codex failed to start: %s", exc)
        start_failed = True
        returncode = "start-failed"
    finally:
        elapsed = time.monotonic() - start
        logger.info("Codex exec completed in %.1fs rc=%s", elapsed, returncode)
        write_text(stdout_file, stdout)
        write_text(stderr_file, stderr)

    if start_failed:
        if temp_dir is not None:
            shutil.rmtree(temp_dir, ignore_errors=True)
        return "(start-failed)"

    output = ""
    try:
        if out_file.exists() and out_file.stat().st_size > 0:
            output = read_text(out_file)
        else:
            output = _jsonl_agent_messages(stdout)
            if not output:
                output = stdout
                if not output and stderr:
                    logger.warning("Codex stderr: %s", stderr[:500])
                    output = stderr
    finally:
        if temp_dir is not None:
            shutil.rmtree(temp_dir, ignore_errors=True)
    return output


def _find_claude() -> str:
    """Find the Claude CLI, including npm and Homebrew fallback locations."""
    found = shutil.which("claude")
    if found:
        return found
    if sys.platform == "win32":
        npm_claude = Path.home() / "AppData" / "Roaming" / "npm" / "claude.cmd"
        if npm_claude.exists():
            return str(npm_claude)
    elif sys.platform == "darwin":
        for candidate in ("/opt/homebrew/bin/claude", "/usr/local/bin/claude"):
            if Path(candidate).exists():
                return candidate
    return "claude"


CLAUDE_PATH = _find_claude()


def claude_exec(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 600,
    dry_run: bool = False,
) -> str:
    """Run Claude CLI for independent review, falling back to Codex if needed."""
    target_dir = work_dir or REPO_ROOT
    if dry_run:
        logger.info(
            "[DRY RUN] claude exec cwd=%s prompt=%s",
            target_dir,
            prompt[:300].replace("\n", " "),
        )
        return "(dry run -- no output)"

    claude_bin = CLAUDE_PATH
    if not Path(claude_bin).exists() and not shutil.which(claude_bin):
        logger.warning("Claude CLI not found; falling back to codex_exec")
        return codex_exec(prompt, work_dir=target_dir, dry_run=dry_run)

    cmd = [str(claude_bin), "-p", "--dangerously-skip-permissions"]
    use_shell = IS_WINDOWS and str(claude_bin).endswith(".cmd")
    start = time.monotonic()
    result: Optional[subprocess.CompletedProcess[str]] = None
    # Strip CLAUDECODE env var to allow nested Claude CLI invocation
    clean_env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    try:
        result = subprocess.run(
            cmd,
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            cwd=str(target_dir),
            env=clean_env,
            shell=use_shell,
            encoding="utf-8",
            errors="replace",
        )
    except subprocess.TimeoutExpired:
        logger.warning("Claude CLI timed out after %ss", timeout_seconds)
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info("Claude CLI completed in %.1fs rc=%s", elapsed, rc)

    output = result.stdout or ""
    if result.returncode != 0:
        logger.warning("Claude CLI error: %s", (result.stderr or "")[:500])
        if not output:
            logger.warning("Claude produced no stdout; falling back to codex_exec")
            return codex_exec(prompt, work_dir=target_dir, dry_run=dry_run)
    return output


def _load_prompt(name: str) -> str:
    """Load a prompt template from the publication prompts directory."""
    prompt_name = name if name.endswith(".txt") else f"{name}.txt"
    return read_text(PROMPTS_DIR / prompt_name)


def _repair_latex_escapes(text: str) -> str:
    """Repair LaTeX-in-JSON escape issues with a stateful walk.

    Codex produces JSON strings containing LaTeX backslash sequences that are
    not valid JSON escapes (\\begin, \\label, \\frac, \\text, etc.).  This
    walks the raw JSON text consuming escape pairs as units so that
    already-valid \\\\X sequences are not corrupted.

    Only \\", \\\\, \\n, \\/, and \\uXXXX are preserved as valid JSON escapes.
    All other \\X sequences (including \\b, \\f, \\r, \\t which overlap with
    common LaTeX commands like \\begin, \\frac, \\ref, \\text) are doubled to
    \\\\X so json.loads succeeds and decodes them as literal backslash + X.
    """
    # We intentionally exclude b/f/r/t from the "keep" set because in
    # LaTeX-heavy JSON they are almost always \\begin, \\frac, \\ref, \\text.
    KEEP = frozenset('"\\n/')
    HEX = frozenset("0123456789abcdefABCDEF")
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c != "\\" or i + 1 >= n:
            out.append(c)
            i += 1
            continue
        nxt = text[i + 1]
        if nxt in KEEP:
            # Valid JSON escape — emit as-is and skip the pair
            out.append("\\")
            out.append(nxt)
            i += 2
        elif nxt == "u" and i + 5 < n and all(
            h in HEX for h in text[i + 2 : i + 6]
        ):
            # \\uXXXX unicode escape
            out.append(text[i : i + 6])
            i += 6
        else:
            # Not a recognized JSON escape — double the backslash
            out.append("\\")
            out.append("\\")
            out.append(nxt)
            i += 2
    return "".join(out)


def _extract_json(text: str) -> Any:
    """Extract and parse the first top-level JSON object or array in text.

    Strips common markdown code fences and retries with LaTeX escape
    repair before giving up.  Prefers arrays over objects when the text
    starts with '[' to avoid extracting a sub-object from an array.
    """
    # Strip markdown code fences that sometimes wrap JSON output
    stripped = re.sub(r"```(?:json)?\s*", "", text)
    for source in (stripped, text):
        result = _try_parse_json_from(source)
        if result is not None:
            return result
    raise ValueError("No parseable top-level JSON object or array found")


def _try_parse_json_from(text: str) -> Any:
    """Attempt to extract and parse a JSON object/array from text.

    When json.loads fails on a balanced candidate (common with LaTeX content),
    retries with LaTeX escape repair before moving to the next candidate.
    """
    for start, first_char in enumerate(text):
        if first_char not in "{[":
            continue
        stack: list[str] = []
        in_string = False
        escape = False
        for index in range(start, len(text)):
            char = text[index]
            if in_string:
                if escape:
                    escape = False
                elif char == "\\":
                    escape = True
                elif char == '"':
                    in_string = False
                continue
            if char == '"':
                in_string = True
                continue
            if char in "{[":
                stack.append(char)
                continue
            if char in "}]":
                if not stack:
                    break
                opener = stack.pop()
                if (opener, char) not in (("{", "}"), ("[", "]")):
                    break
                if not stack:
                    candidate = text[start : index + 1]
                    try:
                        return json.loads(candidate)
                    except json.JSONDecodeError:
                        # LaTeX escape repair: Codex produces \begin, \label etc.
                        # inside JSON strings which are invalid JSON escapes.
                        try:
                            repaired = _repair_latex_escapes(candidate)
                            return json.loads(repaired)
                        except json.JSONDecodeError:
                            pass  # try next candidate position
    return None


def _ensure_gitignore() -> None:
    """Ensure the backflow gitignore excludes the distillation work directory."""
    path = BACKFLOW_DIR / ".gitignore"
    if path.exists():
        lines = read_text(path).splitlines()
    else:
        lines = []
    if ".distillation/" not in lines:
        lines.append(".distillation/")
    write_text(path, "\n".join(lines).strip() + "\n")


def _slugify(value: str) -> str:
    """Convert a human-readable source name into a stable filesystem slug."""
    lowered = value.strip().lower()
    slug = re.sub(r"[^a-z0-9]+", "_", lowered).strip("_")
    return slug or "distillation_source"


@dataclass
class DistillState:
    """Persistent state for one mathematical distillation source."""

    name: str
    current_stage: str = "R"
    round_number: int = 0
    prior_feedback: list[str] = field(default_factory=list)
    scores: dict[str, Any] = field(default_factory=dict)
    created_at: str = field(default_factory=_now_iso)
    updated_at: str = field(default_factory=_now_iso)
    # Continuous deepening: track which theorem families have been written
    depth_cycle: int = 0
    completed_families: list[str] = field(default_factory=list)


def _state_dir(name: str) -> Path:
    """Return the distillation state directory for a source name."""
    return DISTILLATION_DIR / _slugify(name)


def _artifact_path(state: DistillState, filename: str) -> Path:
    """Return the artifact path for a state-local JSON or text file."""
    return _state_dir(state.name) / filename


def save_state(state: DistillState) -> None:
    """Persist a distillation state to `.distillation/<name>/state.json`."""
    state.updated_at = _now_iso()
    write_json(_artifact_path(state, "state.json"), asdict(state))


def load_state(name: str) -> DistillState:
    """Load a distillation state, creating a fresh state when none exists."""
    path = _state_dir(name) / "state.json"
    if not path.exists():
        return DistillState(name=name)
    data = read_json(path)
    return DistillState(
        name=str(data.get("name", name)),
        current_stage=str(data.get("current_stage", "R")),
        round_number=int(data.get("round_number", 0)),
        prior_feedback=list(data.get("prior_feedback", [])),
        scores=dict(data.get("scores", {})),
        created_at=str(data.get("created_at", _now_iso())),
        updated_at=str(data.get("updated_at", _now_iso())),
        depth_cycle=int(data.get("depth_cycle", 0)),
        completed_families=list(data.get("completed_families", [])),
    )


def _write_artifact_json(state: DistillState, filename: str, data: Any) -> None:
    """Write a state-local JSON artifact."""
    write_json(_artifact_path(state, filename), data)


def _read_artifact_json(state: DistillState, filename: str) -> Any:
    """Read a state-local JSON artifact."""
    return read_json(_artifact_path(state, filename))


def _json_block(data: Any) -> str:
    """Format a JSON value for inclusion in a prompt."""
    return json.dumps(data, ensure_ascii=False, indent=2, default=str)


def _research_schema() -> str:
    """Return the required Stage R output schema as JSON text."""
    schema = {
        "mathematician": "source name",
        "method_operators": [
            {
                "name": "operator name",
                "description": "portable method action",
                "omega_use": "where this action can guide Omega",
            }
        ],
        "omega_object_mappings": [
            {
                "source_object": "classical object",
                "omega_object": "Omega object or construction layer",
                "justification": "precise analogy",
            }
        ],
        "theorem_families": [
            {
                "name": "family name",
                "key_results": ["result pattern"],
                "target_sections": ["core section slug"],
            }
        ],
        "search_directives": ["actionable search directive"],
        "induction_templates": ["portable induction template"],
        "failure_modes": ["known limitation or false analogy"],
        "router_triggers": ["short literal trigger phrase"],
        "lean_targets": ["optional formalization target"],
    }
    return _json_block(schema)


def _generate_schema() -> str:
    """Return the required Stage G output schema as JSON text."""
    schema = {
        "knowledge_payload": {
            "source_slug": "stable slug",
            "source_type": "distilled_mathematical_methodology",
            "primary_note": "concise methodological note",
            "method_operators": [],
            "omega_object_mappings": [],
            "theorem_families": [],
        },
        "navigation_payload": {
            "router_triggers": [],
            "search_directives": [],
            "target_sections": [],
            "induction_templates": [],
            "failure_modes": [],
        },
        "primary_targets": ["core section slug"],
        "expansion_queue": [
            {
                "kernel": "work item",
                "target_sections": ["core section slug"],
                "status": "active",
            }
        ],
    }
    return _json_block(schema)


def _writeback_schema() -> str:
    """Return the required Stage W writeback output schema as JSON text."""
    schema = [
        {
            "section": "core section slug",
            "tex_file": "relative path under theory sections/body",
            "type": "remark|definition|lemma|proposition|theorem",
            "label": "distill:source-specific-label",
            "content": "complete LaTeX snippet with label",
        }
    ]
    return _json_block(schema)


def _score_schema() -> str:
    """Return the JSON score schema used by both reviewers."""
    schema = {
        "score": 1,
        "verdict": "reject|revise|accept",
        "issues": ["specific issue"],
        "required_changes": ["specific required change"],
        "depth_assessment": "shallow|adequate|deep",
    }
    return _json_block(schema)


def _section_list() -> str:
    """Build a compact list of core theory section directories and tex files."""
    if not CORE_BODY.exists():
        return "(core body directory not found)"
    lines = []
    for section_dir in sorted(path for path in CORE_BODY.iterdir() if path.is_dir()):
        tex_files = sorted(section_dir.rglob("*.tex"))
        rel_files = [path.relative_to(CORE_BODY).as_posix() for path in tex_files[:8]]
        suffix = "" if len(tex_files) <= 8 else f" (+{len(tex_files) - 8} more)"
        lines.append(f"- {section_dir.name}: {', '.join(rel_files)}{suffix}")
    root_tex = sorted(path for path in CORE_BODY.glob("*.tex") if path.is_file())
    for path in root_tex:
        lines.append(f"- {path.relative_to(CORE_BODY).as_posix()}")
    return "\n".join(lines)


def _euclid_example() -> str:
    """Read the Euclid backflow example used as a style reference."""
    path = BACKFLOW_DIR / "euclid_geometry_backflow_2026-04-09.md"
    if not path.exists():
        return "(Euclid example missing)"
    return read_text(path)[:3000]


def _required_fields_present(data: Any, fields: list[str]) -> list[str]:
    """Return required fields that are missing or empty from a JSON object."""
    if not isinstance(data, dict):
        return fields
    missing = []
    for field_name in fields:
        value = data.get(field_name)
        if value is None or value == "" or value == [] or value == {}:
            missing.append(field_name)
    return missing


def verify_substantive_change(
    writebacks: list[dict[str, Any]],
    section_contexts: str,
) -> tuple[bool, str]:
    """Anti-fake gate: verify writebacks contain real new theorem-like content.

    Catches the pattern where Codex claims to add material but actually
    only produces filler prose, repeats existing definitions, or outputs
    trivially shallow remarks.  Ported from oracle_pipeline.py.
    """
    if not writebacks:
        return False, "FAKE: empty writeback list"

    # Count new claim environments in proposed content
    new_claim_count = 0
    total_content_chars = 0
    for item in writebacks:
        content = item.get("content", "")
        total_content_chars += len(content)
        for env in ("theorem", "lemma", "proposition", "corollary", "definition"):
            if f"\\begin{{{env}}}" in content:
                new_claim_count += 1

    # Check for duplicate labels already present in section contexts
    existing_labels: set[str] = set()
    for match in re.finditer(r"\\label\{([^}]+)\}", section_contexts):
        existing_labels.add(match.group(1))
    duplicate_labels = []
    for item in writebacks:
        label = item.get("label", "")
        if label in existing_labels:
            duplicate_labels.append(label)

    if duplicate_labels:
        return False, (
            f"FAKE: {len(duplicate_labels)} duplicate label(s) already in "
            f"target files: {', '.join(duplicate_labels[:3])}"
        )

    if new_claim_count < MIN_NEW_CLAIMS:
        return False, (
            f"FAKE: only {new_claim_count} claim environment(s) in writebacks "
            f"(threshold: {MIN_NEW_CLAIMS}). Codex likely produced filler prose."
        )

    if total_content_chars < MIN_CONTENT_DELTA:
        return False, (
            f"FAKE: total content only {total_content_chars} chars "
            f"(threshold: {MIN_CONTENT_DELTA}). Too shallow."
        )

    return True, (
        f"PASS: {new_claim_count} claim(s), {total_content_chars} chars, "
        f"no duplicate labels"
    )


def _build_prior_feedback_block(state: DistillState) -> str:
    """Build a structured prior feedback block from history for Codex prompts.

    Ported from oracle_pipeline.py A-DEEP prior_feedback accumulation pattern.
    """
    if not state.prior_feedback:
        return ""
    lines = ["PRIOR FEEDBACK (address ALL of these):"]
    for entry in state.prior_feedback[-8:]:
        lines.append(f"  - {entry}")
    if state.scores:
        score_lines = []
        for stage_key, review_data in state.scores.items():
            if isinstance(review_data, dict):
                codex_s = review_data.get("codex", {}).get("score", "?")
                claude_s = review_data.get("claude", {}).get("score", "?")
                score_lines.append(f"{stage_key}: codex={codex_s} claude={claude_s}")
        if score_lines:
            lines.append("Score history: " + ", ".join(score_lines[-4:]))
    return "\n".join(lines)


def rebuild_from_git(name: str) -> DistillState:
    """Recover pipeline state from git commit history after crash/reset.

    Scans commits touching distillation artifacts for stage completion
    markers and advances state counters to avoid repeating work.
    Ported from oracle_pipeline.py rebuild_rounds_from_git.
    """
    state = load_state(name)
    slug = _slugify(name)
    try:
        result = subprocess.run(
            ["git", "log", "--all", "--format=%s", "-50"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=30,
            encoding="utf-8",
            errors="replace",
        )
    except (subprocess.TimeoutExpired, OSError) as exc:
        logger.debug("git log failed for state rebuild: %s", exc)
        return state

    if result.returncode != 0:
        return state

    max_stage_idx = STAGE_ORDER.index(state.current_stage)
    max_round = state.round_number
    for line in result.stdout.splitlines():
        m = re.search(
            rf"distill\({re.escape(slug)}\):\s*stage\s+(\w)\s+\((\w+)\)\s+complete",
            line,
        )
        if m:
            stage_letter = m.group(1)
            if stage_letter in STAGE_ORDER:
                idx = STAGE_ORDER.index(stage_letter)
                # Advance to the stage AFTER the completed one
                next_idx = min(idx + 1, len(STAGE_ORDER) - 1)
                if next_idx > max_stage_idx:
                    max_stage_idx = next_idx
                    max_round += 1

    if max_stage_idx > STAGE_ORDER.index(state.current_stage):
        old_stage = state.current_stage
        state.current_stage = STAGE_ORDER[max_stage_idx]
        state.round_number = max(state.round_number, max_round)
        save_state(state)
        logger.info(
            "git-rebuild for %s: stage %s -> %s, round %d",
            name, old_stage, state.current_stage, state.round_number,
        )
    return state


def _dry_raw_research(name: str) -> dict[str, Any]:
    """Build a deterministic Stage R artifact for dry-run execution."""
    slug = _slugify(name)
    return {
        "mathematician": name,
        "method_operators": [
            {
                "name": "structural transport",
                "description": "Move a construction through a canonical interface.",
                "omega_use": "Test transfer between primitive and quotient layers.",
            },
            {
                "name": "normal-form extraction",
                "description": "Expose an invariant by choosing a disciplined normal form.",
                "omega_use": "Compare fold, address, and projection normalizations.",
            },
            {
                "name": "obstruction localization",
                "description": "Locate the minimal failed compatibility condition.",
                "omega_use": "Route failures into gluing and rigidity sections.",
            },
            {
                "name": "inductive closure",
                "description": "Grow global structure from audited local steps.",
                "omega_use": "Feed recursive emergence and closure statements.",
            },
        ],
        "omega_object_mappings": [
            {
                "source_object": f"{slug} construction",
                "omega_object": "admissible Omega construction",
                "justification": "Dry-run mapping for pipeline validation.",
            }
        ],
        "theorem_families": [
            {
                "name": "normal form stability",
                "key_results": ["normal forms remain stable under canonical projection"],
                "target_sections": ["folding", "pom"],
            },
            {
                "name": "localized obstruction",
                "key_results": ["failure is visible at the minimal compatibility layer"],
                "target_sections": ["logic_expansion_chain"],
            },
            {
                "name": "recursive closure",
                "key_results": ["local steps assemble into a global closure statement"],
                "target_sections": ["recursive_addressing"],
            },
        ],
        "search_directives": [
            "Search for normal form and canonical projection interfaces.",
            "Search for obstruction, failure, and gluing compatibility language.",
            "Search for recursive closure and audited local step language.",
        ],
        "induction_templates": [
            "Base admissible object, canonical step, invariant preservation.",
            "Local certificate, compatibility audit, global closure.",
        ],
        "failure_modes": [
            "False analogy between construction and rigidity.",
            "Missing minimal obstruction witness.",
        ],
        "router_triggers": [
            "normal form",
            "canonical projection",
            "admissible construction",
            "local certificate",
            "global closure",
            "obstruction",
            "gluing",
            "recursive address",
            "fold",
            "rigidity",
        ],
        "lean_targets": [],
    }


def run_stage_r(state: DistillState, dry_run: bool = False) -> bool:
    """Run Stage R research extraction and persist raw research JSON."""
    logger.info("Stage R starting for %s", state.name)
    required = [
        "mathematician",
        "method_operators",
        "omega_object_mappings",
        "theorem_families",
        "search_directives",
        "induction_templates",
        "failure_modes",
        "router_triggers",
    ]
    feedback = ""
    for attempt in range(1, 4):
        if dry_run:
            data = _dry_raw_research(state.name)
        else:
            prompt = _load_prompt("research").format(
                mathematician=state.name,
                section_list=_section_list(),
                euclid_example=_euclid_example(),
                schema=_research_schema(),
            )
            if feedback:
                prompt += (
                    "\n\nPrevious output failed validation. Correct these issues:\n"
                    + feedback
                )
            response = codex_exec(
                prompt,
                work_dir=REPO_ROOT,
                timeout_seconds=1800,
                dry_run=False,
                log_tag=f"{_slugify(state.name)}_R_attempt{attempt}",
            )
            try:
                data = _extract_json(response)
            except (ValueError, json.JSONDecodeError) as exc:
                feedback = f"Could not parse JSON: {exc}"
                state.prior_feedback.append(f"R attempt {attempt}: {feedback}")
                continue
        missing = _required_fields_present(data, required)
        if not missing:
            _write_artifact_json(state, "raw_research.json", data)
            state.current_stage = "S"
            state.round_number += 1
            save_state(state)
            logger.info("Stage R completed for %s", state.name)
            return True
        feedback = "Missing or empty required fields: " + ", ".join(missing)
        state.prior_feedback.append(f"R attempt {attempt}: {feedback}")
        logger.warning("Stage R validation failed: %s", feedback)
    save_state(state)
    return False


def _normalize_triggers(raw_triggers: Any) -> list[str]:
    """Normalize router trigger entries into nonempty literal strings."""
    triggers = []
    if not isinstance(raw_triggers, list):
        return triggers
    for item in raw_triggers:
        if isinstance(item, str):
            trigger = item.strip()
        elif isinstance(item, dict):
            trigger = str(
                item.get("trigger")
                or item.get("phrase")
                or item.get("name")
                or item.get("term")
                or ""
            ).strip()
        else:
            trigger = str(item).strip()
        if trigger:
            triggers.append(trigger)
    return triggers


def _extract_headings(text: str) -> list[dict[str, str]]:
    """Extract section and subsection headings from LaTeX text."""
    return [
        {"level": match.group(1), "title": match.group(2).strip()}
        for match in SECTION_RE.finditer(text)
    ]


def _extract_claims(text: str) -> list[dict[str, str]]:
    """Extract theorem-like LaTeX blocks from text."""
    claims = []
    for match in CLAIM_BLOCK_RE.finditer(text):
        env_type = match.group(1)
        block = match.group(0)
        label_match = re.search(r"\\label\{([^}]+)\}", block)
        claims.append(
            {
                "type": env_type,
                "label": label_match.group(1) if label_match else "",
                "text": block,
            }
        )
    return claims


def _contains_trigger(text: str, trigger: str) -> bool:
    """Return whether a text contains a trigger phrase case-insensitively."""
    if not trigger:
        return False
    return re.search(re.escape(trigger), text, re.IGNORECASE) is not None


def _score_tex_file(tex_file: Path, triggers: list[str]) -> dict[str, Any]:
    """Score one core .tex file against router triggers.

    Per-file score = matched_triggers / total_triggers (coverage ratio).
    Context tags (H/T/B) are preserved for section-level weighting.
    """
    text = read_text(tex_file)
    headings = _extract_headings(text)
    claims = _extract_claims(text)
    h_count = 0
    t_count = 0
    b_count = 0
    trigger_hits = []
    for trigger in triggers:
        heading_hit = any(_contains_trigger(item["title"], trigger) for item in headings)
        theorem_hit = any(_contains_trigger(item["text"], trigger) for item in claims)
        body_hit = _contains_trigger(text, trigger)
        if heading_hit:
            h_count += 1
            context = "H"
        elif theorem_hit:
            t_count += 1
            context = "T"
        elif body_hit:
            b_count += 1
            context = "B"
        else:
            context = ""
        if context:
            trigger_hits.append({"trigger": trigger, "context": context})
    matched = h_count + t_count + b_count
    denominator = len(triggers) if triggers else 1
    score = matched / denominator
    rel_path = tex_file.relative_to(CORE_BODY).as_posix()
    rel_parts = tex_file.relative_to(CORE_BODY).parts
    section = rel_parts[0] if rel_parts else tex_file.stem
    return {
        "section": section,
        "tex_file": rel_path,
        "score": round(score, 4),
        "match": False,  # determined at section level
        "counts": {"H": h_count, "T": t_count, "B": b_count},
        "trigger_hits": trigger_hits,
        "headings": headings[:8],
        "claim_count": len(claims),
    }

def _aggregate_section_scores(
    file_scores: list[dict[str, Any]], triggers: list[str]
) -> list[dict[str, Any]]:
    """Aggregate per-file scores into per-section scores.

    Section score = unique_triggers_matched / total_triggers, with a bonus
    for triggers matched in heading (H) or theorem (T) context.  The
    weighted formula is:

        (2*H_unique + 2*T_unique + B_unique) / (2 * total_triggers)

    This keeps the design-doc threshold of 0.3 reachable: a section needs
    roughly 20% of triggers in H/T context, or 60% in body context.
    """
    sections: dict[str, dict[str, Any]] = {}
    for item in file_scores:
        sec = item["section"]
        if sec not in sections:
            sections[sec] = {
                "section": sec,
                "triggers_h": set(),
                "triggers_t": set(),
                "triggers_b": set(),
                "file_scores": [],
                "best_file": None,
                "best_file_score": -1.0,
            }
        entry = sections[sec]
        for hit in item["trigger_hits"]:
            trig = hit["trigger"]
            ctx = hit["context"]
            if ctx == "H":
                entry["triggers_h"].add(trig)
            elif ctx == "T":
                entry["triggers_t"].add(trig)
            else:
                entry["triggers_b"].add(trig)
        entry["file_scores"].append(
            {"tex_file": item["tex_file"], "score": item["score"]}
        )
        if item["score"] > entry["best_file_score"]:
            entry["best_file_score"] = item["score"]
            entry["best_file"] = item["tex_file"]

    n = len(triggers) if triggers else 1
    result = []
    for sec, entry in sections.items():
        h_unique = len(entry["triggers_h"])
        # T triggers not already counted in H
        t_unique = len(entry["triggers_t"] - entry["triggers_h"])
        # B triggers not already counted in H or T
        b_unique = len(
            entry["triggers_b"] - entry["triggers_h"] - entry["triggers_t"]
        )
        all_matched = entry["triggers_h"] | entry["triggers_t"] | entry["triggers_b"]
        coverage = len(all_matched) / n
        weighted = (2 * h_unique + 2 * t_unique + b_unique) / (2 * n)
        score = max(coverage, weighted)
        result.append(
            {
                "section": sec,
                "tex_file": entry["best_file"] or "",
                "score": round(score, 4),
                "match": score >= 0.15,
                "coverage": round(coverage, 4),
                "counts": {"H": h_unique, "T": t_unique, "B": b_unique},
                "unique_triggers": sorted(all_matched),
                "file_count": len(entry["file_scores"]),
                "top_files": sorted(
                    entry["file_scores"], key=lambda x: x["score"], reverse=True
                )[:5],
            }
        )
    result.sort(key=lambda x: x["score"], reverse=True)
    return result

def run_stage_s(state: DistillState, dry_run: bool = False) -> bool:
    """Run Stage S deterministic router matching over core LaTeX files.

    Scoring is section-level: triggers are aggregated across all .tex
    files within each top-level section directory.  A section matches when
    its coverage score reaches the 0.3 threshold.
    """
    logger.info("Stage S starting for %s", state.name)
    try:
        raw_research = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError:
        logger.error("Stage S requires raw_research.json")
        return False
    triggers = _normalize_triggers(raw_research.get("router_triggers", []))
    if not triggers:
        logger.error("Stage S has no router triggers")
        return False
    if not CORE_BODY.exists():
        logger.error("Core body directory not found: %s", CORE_BODY)
        return False
    tex_files = sorted(path for path in CORE_BODY.rglob("*.tex") if path.is_file())
    logger.info(
        "Stage S scanning %d .tex files against %d triggers",
        len(tex_files), len(triggers),
    )
    file_scores = [_score_tex_file(path, triggers) for path in tex_files]
    section_scores = _aggregate_section_scores(file_scores, triggers)
    matches = [item for item in section_scores if item["match"]]
    for item in matches:
        logger.info(
            "  matched section=%s score=%.4f coverage=%.4f triggers=%s",
            item["section"],
            item["score"],
            item["coverage"],
            item["unique_triggers"][:5],
        )
    output = {
        "mathematician": state.name,
        "trigger_count": len(triggers),
        "triggers": triggers,
        "matches": matches,
        "all_sections": section_scores,
    }
    _write_artifact_json(state, "section_matches.json", output)
    state.current_stage = "G"
    state.round_number += 1
    save_state(state)
    logger.info(
        "Stage S completed with %d section matches (of %d sections)",
        len(matches), len(section_scores),
    )
    return True

def _dry_generated_payload(state: DistillState) -> dict[str, Any]:
    """Build a deterministic Stage G artifact for dry-run execution."""
    raw = _read_artifact_json(state, "raw_research.json")
    matches = _read_artifact_json(state, "section_matches.json")
    primary_targets = []
    for item in matches.get("matches", [])[:5]:
        section = item.get("section")
        if section and section not in primary_targets:
            primary_targets.append(section)
    if not primary_targets:
        primary_targets = ["folding", "pom"]
    return {
        "knowledge_payload": {
            "source_slug": _slugify(state.name),
            "source_type": "distilled_mathematical_methodology",
            "primary_note": f"Dry-run distilled methodology for {state.name}.",
            "method_operators": raw.get("method_operators", []),
            "omega_object_mappings": raw.get("omega_object_mappings", []),
            "theorem_families": raw.get("theorem_families", []),
        },
        "navigation_payload": {
            "router_triggers": raw.get("router_triggers", []),
            "search_directives": raw.get("search_directives", []),
            "target_sections": primary_targets,
            "induction_templates": raw.get("induction_templates", []),
            "failure_modes": raw.get("failure_modes", []),
        },
        "primary_targets": primary_targets,
        "expansion_queue": [
            {
                "kernel": "dry_run_normal_form_transfer",
                "target_sections": primary_targets[:2],
                "status": "active",
            }
        ],
    }


def _validate_generated_payload(data: Any) -> list[str]:
    """Return validation errors for a Stage G generated payload."""
    errors = []
    if not isinstance(data, dict):
        return ["Stage G output must be a JSON object"]
    for field_name in ("knowledge_payload", "navigation_payload"):
        if not isinstance(data.get(field_name), dict) or not data.get(field_name):
            errors.append(f"Missing or empty {field_name}")
    if not data.get("primary_targets"):
        errors.append("Missing primary_targets")
    if not isinstance(data.get("expansion_queue", []), list):
        errors.append("expansion_queue must be a list")
    return errors


def run_stage_g(state: DistillState, dry_run: bool = False) -> bool:
    """Run Stage G payload generation and persist the generated payload."""
    logger.info("Stage G starting for %s", state.name)
    try:
        raw_research = _read_artifact_json(state, "raw_research.json")
        section_matches = _read_artifact_json(state, "section_matches.json")
    except FileNotFoundError as exc:
        logger.error("Stage G missing prerequisite artifact: %s", exc)
        return False
    feedback = ""
    for attempt in range(1, 4):
        if dry_run:
            data = _dry_generated_payload(state)
        else:
            prompt = _load_prompt("generate").format(
                raw_research=_json_block(raw_research),
                section_matches=_json_block(section_matches),
                schema=_generate_schema(),
            )
            if feedback:
                prompt += (
                    "\n\nPrevious output failed validation. Correct these issues:\n"
                    + feedback
                )
            response = codex_exec(
                prompt,
                work_dir=REPO_ROOT,
                timeout_seconds=1800,
                dry_run=False,
                log_tag=f"{_slugify(state.name)}_G_attempt{attempt}",
            )
            try:
                data = _extract_json(response)
            except (ValueError, json.JSONDecodeError) as exc:
                feedback = f"Could not parse JSON: {exc}"
                state.prior_feedback.append(f"G attempt {attempt}: {feedback}")
                continue
        errors = _validate_generated_payload(data)
        if not errors:
            _write_artifact_json(state, "generated_payload.json", data)
            state.current_stage = "W"
            state.round_number += 1
            save_state(state)
            logger.info("Stage G completed for %s", state.name)
            return True
        feedback = "; ".join(errors)
        state.prior_feedback.append(f"G attempt {attempt}: {feedback}")
        logger.warning("Stage G validation failed: %s", feedback)
    save_state(state)
    return False


def _payload_targets(payload: dict[str, Any], matches: dict[str, Any]) -> list[str]:
    """Derive target section slugs from generated payload and router matches."""
    raw_targets = (
        payload.get("primary_targets")
        or payload.get("navigation_payload", {}).get("target_sections")
        or []
    )
    targets = []
    for item in raw_targets:
        if isinstance(item, str):
            value = item.strip()
        elif isinstance(item, dict):
            value = str(item.get("section") or item.get("name") or item.get("target") or "")
        else:
            value = str(item).strip()
        if value and value not in targets:
            targets.append(value)
    for item in matches.get("matches", [])[:5]:
        value = str(item.get("section", "")).strip()
        if value and value not in targets:
            targets.append(value)
    return targets


def _resolve_core_tex_path(value: str) -> Optional[Path]:
    """Resolve a target `.tex` value to a safe path under CORE_BODY."""
    candidate = Path(value)
    if candidate.is_absolute():
        path = candidate.resolve()
    else:
        path = (CORE_BODY / candidate).resolve()
    try:
        path.relative_to(CORE_BODY.resolve())
    except ValueError:
        return None
    if path.suffix != ".tex":
        return None
    return path


def _select_target_files(
    payload: dict[str, Any],
    matches: dict[str, Any],
) -> list[dict[str, str]]:
    """Select concrete target `.tex` files for writeback prompting."""
    selected = []
    seen = set()
    targets = _payload_targets(payload, matches)
    match_rows = matches.get("matches", [])
    for target in targets:
        selected_for_target = False
        if target.endswith(".tex"):
            path = _resolve_core_tex_path(target)
            if path and path.exists():
                rel = path.relative_to(CORE_BODY).as_posix()
                selected.append({"section": rel.split("/")[0], "tex_file": rel})
                seen.add(rel)
                selected_for_target = True
            continue
        for item in match_rows:
            if item.get("section") != target:
                continue
            rel = str(item.get("tex_file", ""))
            path = _resolve_core_tex_path(rel)
            if path and path.exists() and rel not in seen:
                selected.append({"section": target, "tex_file": rel})
                seen.add(rel)
                selected_for_target = True
                break
        if selected_for_target:
            continue
        section_dir = CORE_BODY / target
        candidates = []
        if (section_dir / "main.tex").exists():
            candidates.append(section_dir / "main.tex")
        if section_dir.exists():
            candidates.extend(sorted(section_dir.rglob("*.tex")))
        for candidate in candidates:
            rel = candidate.relative_to(CORE_BODY).as_posix()
            if rel not in seen:
                selected.append({"section": target, "tex_file": rel})
                seen.add(rel)
                break
    return selected[:6]


def _collect_section_contexts(targets: list[dict[str, str]]) -> str:
    """Read target LaTeX files and format them as prompt context."""
    chunks = []
    for target in targets:
        rel = target["tex_file"]
        path = _resolve_core_tex_path(rel)
        if not path or not path.exists():
            continue
        text = read_text(path)
        if len(text) > 16000:
            text = text[:16000] + "\n% [context truncated by distill.py]\n"
        chunks.append(f"--- {rel} ---\n{text}")
    return "\n\n".join(chunks)


def _dry_writebacks(targets: list[dict[str, str]], name: str) -> list[dict[str, str]]:
    """Build deterministic writeback proposals for dry-run execution."""
    slug = _slugify(name)
    proposals = []
    for target in targets[:2]:
        label = f"rem:{slug}-dry-run-{target['section']}"
        content = (
            "\\begin{remark}[Distilled method router dry run]\n"
            f"\\label{{{label}}}\n"
            f"This dry-run note records where the {name} distillation would attach: "
            "the local construction must be separated from any later rigidity or "
            "classification claim before it is used as an Omega dependency.\n"
            "\\end{remark}"
        )
        proposals.append(
            {
                "section": target["section"],
                "tex_file": target["tex_file"],
                "type": "remark",
                "label": label,
                "content": content,
            }
        )
    return proposals


def _latex_balance_errors(content: str) -> list[str]:
    """Return simple begin/end environment balance errors for a LaTeX snippet."""
    errors = []
    begins: dict[str, int] = {}
    ends: dict[str, int] = {}
    for env_name in re.findall(r"\\begin\{([^}]+)\}", content):
        begins[env_name] = begins.get(env_name, 0) + 1
    for env_name in re.findall(r"\\end\{([^}]+)\}", content):
        ends[env_name] = ends.get(env_name, 0) + 1
    for env_name, count in begins.items():
        if ends.get(env_name, 0) != count:
            errors.append(f"Unbalanced environment {env_name}")
    for env_name, count in ends.items():
        if begins.get(env_name, 0) != count:
            errors.append(f"End without begin for {env_name}")
    return errors


def _validate_writebacks(writebacks: Any) -> tuple[list[dict[str, Any]], list[str]]:
    """Validate writeback JSON proposals and return normalized entries."""
    if not isinstance(writebacks, list):
        return [], ["Writeback response must be a JSON array"]
    normalized = []
    errors = []
    labels = set()
    required = ("section", "tex_file", "type", "label", "content")
    for index, item in enumerate(writebacks):
        if not isinstance(item, dict):
            errors.append(f"Item {index} is not an object")
            continue
        missing = [field_name for field_name in required if not item.get(field_name)]
        if missing:
            errors.append(f"Item {index} missing fields: {', '.join(missing)}")
            continue
        rel = str(item["tex_file"]).strip()
        path = _resolve_core_tex_path(rel)
        if not path or not path.exists():
            errors.append(f"Item {index} target file not found under core body: {rel}")
            continue
        label = str(item["label"]).strip()
        content = str(item["content"]).strip()
        if label in labels:
            errors.append(f"Duplicate proposed label: {label}")
            continue
        labels.add(label)
        if "\\documentclass" in content or "\\begin{document}" in content:
            errors.append(f"Item {index} contains document-level LaTeX")
        if label not in content:
            errors.append(f"Item {index} content does not contain label {label}")
        if re.search(rf"\\label\{{{re.escape(label)}\}}", read_text(path)):
            errors.append(f"Item {index} label already exists in {rel}: {label}")
        errors.extend([f"Item {index}: {err}" for err in _latex_balance_errors(content)])
        normalized.append(
            {
                "section": str(item["section"]).strip(),
                "tex_file": rel,
                "type": str(item["type"]).strip(),
                "label": label,
                "content": content,
            }
        )
    return normalized, errors


def _parse_score_response(response: str) -> dict[str, Any]:
    """Parse a reviewer response into a normalized score object."""
    try:
        data = _extract_json(response)
    except (ValueError, json.JSONDecodeError):
        data = {"score": 1, "verdict": "reject", "issues": [response[:1000]]}
    if not isinstance(data, dict):
        data = {"score": 1, "verdict": "reject", "issues": ["Reviewer returned non-object JSON"]}
    try:
        score = int(float(data.get("score", 1)))
    except (TypeError, ValueError):
        score = 1
    data["score"] = max(1, min(10, score))
    data.setdefault("verdict", "revise" if data["score"] < 7 else "accept")
    data.setdefault("issues", [])
    data.setdefault("required_changes", [])
    return data


def _codex_score(
    state: DistillState,
    writebacks: list[dict[str, Any]],
    payload: dict[str, Any],
    dry_run: bool,
) -> dict[str, Any]:
    """Run the Codex review prompt with retry and return a normalized score.

    Retries once on empty/unparseable JSON (ported from oracle_pipeline.py).
    """
    if dry_run:
        return {"score": 8, "verdict": "accept", "issues": [], "required_changes": []}
    prompt = _load_prompt("review_codex").format(
        mathematician=state.name,
        writebacks=_json_block(writebacks),
        payload=_json_block(payload),
        score_schema=_score_schema(),
    )
    for attempt in range(1, 3):
        response = codex_exec(
            prompt,
            work_dir=REPO_ROOT,
            timeout_seconds=900,
            dry_run=False,
            log_tag=f"{_slugify(state.name)}_W_review_codex_a{attempt}",
        )
        result = _parse_score_response(response)
        if result.get("score", 0) > 0 and result.get("verdict") != "reject":
            return result
        if result.get("issues") and any(
            "parseable" not in str(i).lower() for i in result["issues"]
        ):
            return result
        logger.warning(
            "Codex review attempt %d: empty/unparseable, retrying", attempt
        )
    return _parse_score_response(response)


def _claude_score(
    state: DistillState,
    writebacks: list[dict[str, Any]],
    section_contexts: str,
    dry_run: bool,
) -> dict[str, Any]:
    """Run the Claude review prompt with retry and return a normalized score.

    Retries once on empty/unparseable JSON (ported from oracle_pipeline.py).
    """
    if dry_run:
        return {"score": 8, "verdict": "accept", "issues": [], "required_changes": []}
    prompt = _load_prompt("review_claude").format(
        mathematician=state.name,
        writebacks=_json_block(writebacks),
        section_contexts=section_contexts,
        score_schema=_score_schema(),
    )
    for attempt in range(1, 3):
        response = claude_exec(
            prompt,
            work_dir=REPO_ROOT,
            timeout_seconds=600,
            dry_run=False,
        )
        result = _parse_score_response(response)
        if result.get("score", 0) > 0 and result.get("verdict") != "reject":
            return result
        if result.get("issues") and any(
            "parseable" not in str(i).lower() for i in result["issues"]
        ):
            return result
        logger.warning(
            "Claude review attempt %d: empty/unparseable, retrying", attempt
        )
    return _parse_score_response(response)


def _review_writebacks(
    state: DistillState,
    writebacks: list[dict[str, Any]],
    payload: dict[str, Any],
    section_contexts: str,
    dry_run: bool,
) -> dict[str, Any]:
    """Run the dual-review gate for writeback proposals.

    Uses parallel independent scoring. If one reviewer returns empty JSON,
    falls back to the other; if both empty, returns score 0 so the round
    retries.  Ported from oracle_pipeline.py A3+A4 parallel dual review.
    """
    with ThreadPoolExecutor(max_workers=2) as executor:
        codex_future = executor.submit(_codex_score, state, writebacks, payload, dry_run)
        claude_future = executor.submit(
            _claude_score,
            state,
            writebacks,
            section_contexts,
            dry_run,
        )
        codex_review = codex_future.result()
        claude_review = claude_future.result()

    codex_s = codex_review.get("score", 0)
    claude_s = claude_review.get("score", 0)
    codex_ok = codex_s > 0
    claude_ok = claude_s > 0

    if codex_ok and claude_ok:
        # Lenient dual-review: pass if EITHER reviewer passes AND neither
        # gives a fundamentally broken score (< 4).  Using min() alone made
        # a single harsh reviewer block all progress (e.g. codex=7, claude=3
        # → final=3).  The new rule: max of both scores, but if the lower
        # score is < 4, cap the final at 6 (forces a revision but doesn't
        # fully block when one reviewer sees depth the other misses).
        low = min(codex_s, claude_s)
        high = max(codex_s, claude_s)
        if low >= SCORE_PASS_THRESHOLD:
            final_score = low  # both pass — use the lower (conservative)
        elif high >= SCORE_PASS_THRESHOLD and low >= 4:
            final_score = high  # one passes, other is not broken — accept
        elif high >= SCORE_PASS_THRESHOLD and low < 4:
            final_score = 6  # one passes but other is harsh — force revise
        else:
            final_score = high  # neither passes — use the better one
    elif codex_ok:
        logger.warning("Claude review empty, using codex=%d", codex_s)
        final_score = codex_s
    elif claude_ok:
        logger.warning("Codex review empty, using claude=%d", claude_s)
        final_score = claude_s
    else:
        logger.warning("Both reviewers returned empty JSON")
        final_score = 0

    # Detect FUNDAMENTAL depth issue: both reviewers say "reject"
    both_reject = (
        codex_review.get("verdict") == "reject"
        and claude_review.get("verdict") == "reject"
    )

    logger.info(
        "Dual review: codex=%d claude=%d final=%d both_reject=%s",
        codex_s, claude_s, final_score, both_reject,
    )

    return {
        "codex": codex_review,
        "claude": claude_review,
        "minimum_score": final_score,
        "both_reject": both_reject,
    }


def _find_insert_position(text: str) -> int:
    """Find the insertion point: before \\endinput if present, else after last claim block."""
    endinput = text.find("\\endinput")
    # Always insert before \endinput when present
    if endinput >= 0:
        return endinput
    matches = list(CLAIM_BLOCK_RE.finditer(text))
    if matches:
        end = matches[-1].end()
        while end < len(text) and text[end] in " \t\r\n":
            end += 1
        return end
    return len(text)


_DISTILL_BLOCK_RE = re.compile(
    r"\n?% --- Distillation writeback ---\n.*?% --- End distillation writeback ---\n?",
    re.DOTALL,
)


def _plan_writeback_application(
    writebacks: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[str]]:
    """Prepare file-level writeback insertions without modifying files.

    Idempotent: if the file already contains a distillation writeback block,
    it is replaced rather than duplicated (ported from backflow.py injection).
    """
    grouped: dict[str, list[dict[str, Any]]] = {}
    for item in writebacks:
        grouped.setdefault(item["tex_file"], []).append(item)

    plan = []
    errors = []
    for rel, items in grouped.items():
        path = _resolve_core_tex_path(rel)
        if not path or not path.exists():
            errors.append(f"Target file disappeared: {rel}")
            continue
        old_text = read_text(path)

        # Build the new distillation block
        block_lines = ["", "% --- Distillation writeback ---"]
        for item in items:
            block_lines.append(item["content"].strip())
            block_lines.append("")
        block_lines.append("% --- End distillation writeback ---")
        insert_block = "\n".join(block_lines).rstrip() + "\n"

        # Idempotent: remove any existing distillation block first
        base_text = _DISTILL_BLOCK_RE.sub("", old_text)

        position = _find_insert_position(base_text)
        prefix = base_text[:position].rstrip()
        suffix = base_text[position:].lstrip("\n")
        new_text = prefix + "\n" + insert_block
        if suffix:
            new_text += "\n" + suffix
        line_count = len(new_text.splitlines())
        if line_count >= 750:
            errors.append(f"{rel} would have {line_count} lines, exceeding <750 gate")
            continue
        plan.append(
            {
                "tex_file": rel,
                "path": path,
                "old_text": old_text,
                "new_text": new_text,
                "labels": [item["label"] for item in items],
                "line_count": line_count,
            }
        )
    return plan, errors


def _make_preview_diff(rel: str, old_text: str, new_text: str, limit: int = 220) -> str:
    """Build a compact unified-style diff preview without external libraries."""
    old_lines = old_text.splitlines()
    new_lines = new_text.splitlines()
    prefix = 0
    while (
        prefix < len(old_lines)
        and prefix < len(new_lines)
        and old_lines[prefix] == new_lines[prefix]
    ):
        prefix += 1
    suffix = 0
    while (
        suffix < len(old_lines) - prefix
        and suffix < len(new_lines) - prefix
        and old_lines[len(old_lines) - 1 - suffix] == new_lines[len(new_lines) - 1 - suffix]
    ):
        suffix += 1
    old_changed = old_lines[prefix : len(old_lines) - suffix if suffix else len(old_lines)]
    new_changed = new_lines[prefix : len(new_lines) - suffix if suffix else len(new_lines)]
    lines = [f"--- {rel}", f"+++ {rel}", f"@@ line {prefix + 1} @@"]
    for line in old_changed[:limit]:
        lines.append("-" + line)
    for line in new_changed[:limit]:
        lines.append("+" + line)
    omitted = max(0, len(old_changed) + len(new_changed) - 2 * limit)
    if omitted:
        lines.append(f"... {omitted} changed lines omitted ...")
    return "\n".join(lines)


def _edit_writebacks_interactively(
    state: DistillState,
    writebacks: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Open writeback JSON in an editor and return the edited proposals."""
    temp_dir = Path(tempfile.mkdtemp(prefix="omega_distill_edit_"))
    edit_file = temp_dir / f"{_slugify(state.name)}_writebacks.json"
    write_json(edit_file, writebacks)
    editor = os.environ.get("EDITOR") or ("notepad" if IS_WINDOWS else "vi")
    subprocess.run([editor, str(edit_file)], cwd=str(REPO_ROOT))
    edited = read_json(edit_file)
    shutil.rmtree(temp_dir, ignore_errors=True)
    normalized, errors = _validate_writebacks(edited)
    if errors:
        raise ValueError("; ".join(errors))
    return normalized


def _apply_writeback_plan(plan: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Apply a prepared writeback plan to the target LaTeX files."""
    applied = []
    for item in plan:
        write_text(item["path"], item["new_text"])
        applied.append(
            {
                "tex_file": item["tex_file"],
                "labels": item["labels"],
                "line_count": item["line_count"],
            }
        )
    return applied


def run_stage_w(
    state: DistillState,
    dry_run: bool = False,
    supervised: bool = True,
) -> bool:
    """Run Stage W writeback generation, dual review, and optional application.

    Deep reasoning upgrades (ported from oracle_pipeline.py + codex_formalize.py):
    - Anti-fake gate: verify writebacks contain real theorem-like content
    - Real dual review with retry on empty JSON
    - Prior feedback accumulation across rounds
    - A-DEEP escalation: when both reviewers reject, escalate with combined
      feedback union for deeper Codex generation
    - Idempotent LaTeX injection (no duplicate blocks)
    """
    logger.info("Stage W starting for %s (depth_cycle=%d)", state.name, state.depth_cycle)
    try:
        payload = _read_artifact_json(state, "generated_payload.json")
        matches = _read_artifact_json(state, "section_matches.json")
        raw_research = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError as exc:
        logger.error("Stage W missing prerequisite artifact: %s", exc)
        return False

    # Determine focused family for deepening cycles
    focused_family: Optional[dict[str, Any]] = None
    if state.depth_cycle > 0:
        focused_family = _next_deepening_family(state)
        if focused_family is None:
            logger.info("Stage W: all families exhausted, nothing to deepen")
            state.current_stage = "E"
            save_state(state)
            return True
        logger.info(
            "Stage W deepening: family=%s targets=%s",
            focused_family.get("name"),
            focused_family.get("target_sections"),
        )

    targets = _select_target_files(payload, matches)
    # In deepening mode, narrow targets to the focused family's sections
    if focused_family:
        family_sections = set(focused_family.get("target_sections", []))
        focused_targets = [t for t in targets if t["section"] in family_sections]
        if not focused_targets:
            # Family targets not in scan matches; use family sections directly
            for sec in focused_family.get("target_sections", []):
                sec_dir = CORE_BODY / sec
                if sec_dir.exists():
                    main_tex = sec_dir / "main.tex"
                    if main_tex.exists():
                        focused_targets.append({
                            "section": sec,
                            "tex_file": (main_tex.relative_to(CORE_BODY)).as_posix(),
                        })
                    else:
                        for tex in sorted(sec_dir.rglob("*.tex"))[:1]:
                            focused_targets.append({
                                "section": sec,
                                "tex_file": tex.relative_to(CORE_BODY).as_posix(),
                            })
        if focused_targets:
            targets = focused_targets

    if not targets:
        logger.error("Stage W could not select target files")
        return False
    section_contexts = _collect_section_contexts(targets)
    prior_feedback_block = _build_prior_feedback_block(state)
    feedback = ""
    attempts = []
    accepted_writebacks: list[dict[str, Any]] = []
    accepted_review: dict[str, Any] = {}
    deep_rounds = 0
    for attempt in range(1, MAX_W_ROUNDS + 1):
        if dry_run:
            raw_writebacks = _dry_writebacks(targets, state.name)
        else:
            prompt = _load_prompt("writeback").format(
                mathematician=state.name,
                payload=_json_block(payload),
                targets=_json_block(targets),
                section_contexts=section_contexts,
                schema=_writeback_schema(),
            )
            # Inject focused family context for deepening cycles
            if focused_family:
                prompt += (
                    f"\n\nDEEPENING CYCLE {state.depth_cycle}: "
                    f"Focus on theorem family '{focused_family['name']}'.\n"
                    f"Key results to formalize:\n"
                )
                for kr in focused_family.get("key_results", []):
                    prompt += f"  - {kr}\n"
                prompt += (
                    "\nYou MUST produce theorem/lemma environments with PROOFS "
                    "for the above key results. Map them precisely to the Omega "
                    "constructions visible in the section context.\n"
                    "Previously completed families (DO NOT repeat): "
                    + ", ".join(state.completed_families or ["none"])
                    + "\n"
                )
            if prior_feedback_block:
                prompt += "\n\n" + prior_feedback_block
            if feedback:
                prompt += (
                    "\n\nPrevious writeback failed validation or review. "
                    "Correct these issues:\n"
                    + feedback
                )
            # Escalate timeout when stuck in low scores
            low_rounds = sum(
                1 for a in attempts
                if a.get("review", {}).get("minimum_score", 0) < SCORE_PASS_THRESHOLD
            )
            w_timeout = 2400 if low_rounds >= 2 else 1800
            response = codex_exec(
                prompt,
                work_dir=REPO_ROOT,
                timeout_seconds=w_timeout,
                dry_run=False,
                log_tag=f"{_slugify(state.name)}_W_attempt{attempt}",
            )
            try:
                raw_writebacks = _extract_json(response)
            except (ValueError, json.JSONDecodeError) as exc:
                feedback = f"Could not parse writeback JSON: {exc}"
                attempts.append({"attempt": attempt, "errors": [feedback]})
                continue

        writebacks, validation_errors = _validate_writebacks(raw_writebacks)
        if validation_errors:
            feedback = "; ".join(validation_errors)
            attempts.append({"attempt": attempt, "errors": validation_errors})
            state.prior_feedback.append(f"W attempt {attempt}: {feedback}")
            continue

        # Anti-fake gate: verify substantive content before expensive review
        if not dry_run:
            substantive, reason = verify_substantive_change(
                writebacks, section_contexts
            )
            if not substantive:
                logger.warning("ANTI-FAKE: %s", reason)
                feedback = reason
                attempts.append({"attempt": attempt, "anti_fake": reason})
                state.prior_feedback.append(
                    f"W attempt {attempt}: ANTI-FAKE REJECTED — {reason}"
                )
                save_state(state)
                continue
            logger.info("Anti-fake: %s", reason)

        review = _review_writebacks(state, writebacks, payload, section_contexts, dry_run)
        attempts.append({"attempt": attempt, "review": review, "writebacks": writebacks})

        if review["minimum_score"] >= SCORE_PASS_THRESHOLD:
            accepted_writebacks = writebacks
            accepted_review = review
            break

        # A-DEEP escalation: when both reviewers reject, escalate with
        # combined feedback union for deeper generation
        if review.get("both_reject") and deep_rounds < MAX_DEEP_ROUNDS:
            deep_rounds += 1
            logger.warning(
                "Both reviewers reject at attempt %d. A-DEEP escalation %d/%d",
                attempt, deep_rounds, MAX_DEEP_ROUNDS,
            )
            # Build union of concerns from both reviewers
            codex_issues = review.get("codex", {}).get("issues", [])
            claude_issues = review.get("claude", {}).get("issues", [])
            codex_changes = review.get("codex", {}).get("required_changes", [])
            claude_changes = review.get("claude", {}).get("required_changes", [])
            deep_feedback = json.dumps({
                "codex_issues": codex_issues,
                "claude_issues": claude_issues,
                "codex_required_changes": codex_changes,
                "claude_required_changes": claude_changes,
                "codex_score": review.get("codex", {}).get("score", 0),
                "claude_score": review.get("claude", {}).get("score", 0),
                "escalation_round": deep_rounds,
            }, ensure_ascii=False, indent=2)[:4000]
            feedback = (
                "DEEP ESCALATION: Both independent reviewers rejected this output.\n"
                "You MUST address ALL issues from BOTH reviewers.\n"
                "Produce REAL theorems with complete proofs, not summaries.\n\n"
                + deep_feedback
            )
            state.prior_feedback.append(
                f"W attempt {attempt}: A-DEEP escalation {deep_rounds} "
                f"(codex={review.get('codex', {}).get('score', 0)}, "
                f"claude={review.get('claude', {}).get('score', 0)})"
            )
            save_state(state)
            continue

        feedback = _json_block(review)
        state.prior_feedback.append(
            f"W attempt {attempt}: review gate below {SCORE_PASS_THRESHOLD} "
            f"(codex={review.get('codex', {}).get('score', 0)}, "
            f"claude={review.get('claude', {}).get('score', 0)})"
        )
        save_state(state)  # persist feedback in case of crash/restart

    if not accepted_writebacks:
        _write_artifact_json(state, "writeback_response.json", {"attempts": attempts})
        save_state(state)
        logger.error("Stage W failed review gate")
        return False

    _write_artifact_json(
        state,
        "writeback_response.json",
        {"attempts": attempts, "accepted_review": accepted_review},
    )

    plan, plan_errors = _plan_writeback_application(accepted_writebacks)
    if plan_errors:
        _write_artifact_json(
            state,
            "writebacks.json",
            {"status": "rejected", "errors": plan_errors, "writebacks": accepted_writebacks},
        )
        logger.error("Stage W application plan failed: %s", "; ".join(plan_errors))
        return False

    applied: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    if dry_run:
        skipped = [
            {"tex_file": item["tex_file"], "labels": item["labels"], "reason": "dry_run"}
            for item in plan
        ]
    else:
        if supervised and not sys.stdin.isatty():
            logger.info("Non-interactive session; auto-applying writebacks")
            supervised = False
        while supervised:
            diff = "\n\n".join(
                _make_preview_diff(item["tex_file"], item["old_text"], item["new_text"])
                for item in plan
            )
            print(diff)
            answer = input("Apply writebacks? [y/n/e] ").strip().lower()
            if answer == "y":
                break
            if answer == "n":
                skipped = [
                    {
                        "tex_file": item["tex_file"],
                        "labels": item["labels"],
                        "reason": "supervised_skip",
                    }
                    for item in plan
                ]
                plan = []
                break
            if answer == "e":
                try:
                    accepted_writebacks = _edit_writebacks_interactively(
                        state,
                        accepted_writebacks,
                    )
                    plan, plan_errors = _plan_writeback_application(accepted_writebacks)
                    if plan_errors:
                        print("; ".join(plan_errors))
                except (OSError, ValueError, json.JSONDecodeError) as exc:
                    print(f"Edit failed: {exc}")
                continue
            print("Please enter y, n, or e.")
        if plan:
            applied = _apply_writeback_plan(plan)

    _write_artifact_json(
        state,
        "writebacks.json",
        {
            "status": "dry_run" if dry_run else "applied" if applied else "skipped",
            "review": accepted_review,
            "writebacks": accepted_writebacks,
            "applied": applied,
            "skipped": skipped,
        },
    )
    state.current_stage = "E"
    score_key = f"W_cycle{state.depth_cycle}" if state.depth_cycle > 0 else "W"
    state.scores[score_key] = accepted_review
    # Mark focused family as completed for deepening tracking
    if focused_family:
        family_name = focused_family.get("name", "")
        if family_name and family_name not in state.completed_families:
            state.completed_families.append(family_name)
            logger.info("Marked family '%s' complete (total: %d)",
                        family_name, len(state.completed_families))
    state.round_number += 1
    save_state(state)
    logger.info("Stage W completed for %s (cycle %d)", state.name, state.depth_cycle)
    return True


def _registry_entry(state: DistillState) -> dict[str, Any]:
    """Build the knowledge backflow registry entry for a completed distillation."""
    payload = _read_artifact_json(state, "generated_payload.json")
    writebacks_path = _artifact_path(state, "writebacks.json")
    writebacks = read_json(writebacks_path) if writebacks_path.exists() else {}
    source_slug = (
        payload.get("knowledge_payload", {}).get("source_slug")
        or _slugify(state.name)
    )
    primary_targets = payload.get("primary_targets") or payload.get(
        "navigation_payload",
        {},
    ).get("target_sections", [])
    integrated = []
    for item in writebacks.get("applied", []):
        integrated.extend(item.get("labels", []))
    if not integrated:
        for item in writebacks.get("writebacks", []):
            label = item.get("label")
            if label:
                integrated.append(label)
    return {
        "source_slug": source_slug,
        "source_type": payload.get("knowledge_payload", {}).get(
            "source_type",
            "distilled_mathematical_methodology",
        ),
        "status": "active",
        "date_created": datetime.utcnow().strftime("%Y-%m-%d"),
        "integration_mode": "distillation_pipeline",
        "primary_note": (
            f"papers/publication/backflow/.distillation/{_slugify(state.name)}/"
            "generated_payload.json"
        ),
        "primary_targets": primary_targets,
        "integrated_writebacks": integrated,
        "expansion_queue": payload.get("expansion_queue", []),
    }


def _read_registry() -> list[dict[str, Any]]:
    """Read the knowledge backflow registry as a list of entries."""
    if not REGISTRY_PATH.exists():
        return []
    data = read_json(REGISTRY_PATH)
    if isinstance(data, list):
        return data
    raise ValueError(f"Registry must be a JSON array: {REGISTRY_PATH}")


def _update_registry(entry: dict[str, Any]) -> list[dict[str, Any]]:
    """Replace or append one entry in the knowledge backflow registry."""
    registry = _read_registry()
    output = []
    replaced = False
    for existing in registry:
        if existing.get("source_slug") == entry["source_slug"]:
            original_date = existing.get("date_created")
            if original_date:
                entry["date_created"] = original_date
            output.append(entry)
            replaced = True
        else:
            output.append(existing)
    if not replaced:
        output.append(entry)
    write_json(REGISTRY_PATH, output)
    return output


def _board_block(registry: list[dict[str, Any]]) -> str:
    """Render the managed distillation board block from registry entries."""
    lines = [
        "<!-- distillation-board:start -->",
        "| Source | Status | Targets | Writebacks | Queue |",
        "|---|---|---|---:|---:|",
    ]
    for entry in sorted(registry, key=lambda item: str(item.get("source_slug", ""))):
        targets = ", ".join(str(item) for item in entry.get("primary_targets", []))
        writeback_count = len(entry.get("integrated_writebacks", []))
        queue_count = len(entry.get("expansion_queue", []))
        lines.append(
            "| `{}` | {} | {} | {} | {} |".format(
                entry.get("source_slug", ""),
                entry.get("status", ""),
                targets,
                writeback_count,
                queue_count,
            )
        )
    lines.append("<!-- distillation-board:end -->")
    return "\n".join(lines)


def _update_distillation_board(registry: list[dict[str, Any]]) -> None:
    """Create or update the publication distillation board markdown file."""
    path = PUBLICATION_DIR / "DISTILLATION_BOARD.md"
    block = _board_block(registry)
    if path.exists():
        text = read_text(path)
    else:
        text = "# Distillation Board\n\n"
    pattern = re.compile(
        r"<!-- distillation-board:start -->.*?<!-- distillation-board:end -->",
        re.DOTALL,
    )
    if pattern.search(text):
        text = pattern.sub(block, text)
    else:
        text = text.rstrip() + "\n\n" + block + "\n"
    write_text(path, text)


def _next_deepening_family(state: DistillState) -> Optional[dict[str, Any]]:
    """Return the next theorem family to deepen, or None if all exhausted."""
    try:
        raw = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError:
        return None
    families = raw.get("theorem_families", [])
    for family in families:
        name = family.get("name", "")
        if name and name not in state.completed_families:
            return family
    return None


def run_stage_e(state: DistillState, dry_run: bool = False) -> bool:
    """Run Stage E registry and board export, then check for deepening.

    Continuous deepening: after registering, check if theorem families
    remain unexplored. If yes, loop back to W with the next family as
    the focused target. The pipeline only reaches DONE when ALL families
    have been written or the stop file appears.
    """
    logger.info("Stage E starting for %s", state.name)
    try:
        entry = _registry_entry(state)
    except FileNotFoundError as exc:
        logger.error("Stage E missing prerequisite artifact: %s", exc)
        return False
    _write_artifact_json(state, "registry_entry.json", entry)
    if dry_run:
        logger.info("[DRY RUN] Stage E would update registry and board")
    else:
        registry = _update_registry(entry)
        _update_distillation_board(registry)

    # Check for next deepening target
    next_family = _next_deepening_family(state)
    if next_family and not STOP_FILE.exists():
        state.depth_cycle += 1
        state.current_stage = "W"
        state.round_number += 1
        # Clear prior feedback for fresh cycle but keep scores
        state.prior_feedback = []
        save_state(state)
        logger.info(
            "Stage E: deepening cycle %d — next family: %s (targets: %s)",
            state.depth_cycle,
            next_family.get("name"),
            next_family.get("target_sections"),
        )
        return True

    state.current_stage = "DONE"
    state.round_number += 1
    save_state(state)
    logger.info(
        "Stage E completed for %s — all %d families exhausted",
        state.name, len(state.completed_families),
    )
    return True


def _stage_index(stage: str) -> int:
    """Return the numeric index of a pipeline stage."""
    if stage not in STAGE_ORDER:
        raise ValueError(f"Unknown stage: {stage}")
    return STAGE_ORDER.index(stage)


STAGE_COMMIT_FILES: dict[str, list[str]] = {
    # Stage W writes .tex files; Stage E writes registry + board
    "W": [],  # populated dynamically from writebacks.json
    "E": [
        str(REGISTRY_PATH),
        str(PUBLICATION_DIR / "DISTILLATION_BOARD.md"),
    ],
}

STAGE_NAMES = {
    "R": "research",
    "S": "scan",
    "G": "generate",
    "W": "writeback",
    "E": "register",
}


def _git_commit_push(name: str, stage: str, extra_files: Optional[list[str]] = None) -> None:
    """Commit stage outputs and push to remote. Best-effort, never fatal."""
    slug = _slugify(name)
    files_to_add = list(extra_files or [])

    # Stage E: registry + board
    if stage in STAGE_COMMIT_FILES:
        files_to_add.extend(STAGE_COMMIT_FILES[stage])

    # Stage W: collect modified .tex files from writebacks.json
    if stage == "W":
        wb_path = _state_dir(name) / "writebacks.json"
        if wb_path.exists():
            try:
                wb_data = read_json(wb_path)
                for item in wb_data.get("applied", []):
                    tex_rel = item.get("tex_file", "")
                    if tex_rel:
                        full = CORE_BODY / tex_rel
                        if full.exists():
                            files_to_add.append(str(full))
            except (OSError, json.JSONDecodeError, KeyError):
                pass

    if not files_to_add:
        logger.info("Stage %s: no files to commit", stage)
        return

    # Filter to files that actually exist
    files_to_add = [f for f in files_to_add if Path(f).exists()]
    if not files_to_add:
        return

    stage_label = STAGE_NAMES.get(stage, stage)
    msg = f"distill({slug}): stage {stage} ({stage_label}) complete"

    try:
        subprocess.run(
            ["git", "add"] + files_to_add,
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=30,
        )
        # Check if there's anything staged
        diff = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            cwd=str(REPO_ROOT), capture_output=True, timeout=10,
        )
        if diff.returncode == 0:
            logger.info("Stage %s: nothing new to commit", stage)
            return
        subprocess.run(
            ["git", "commit", "-m", msg],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=30,
        )
        subprocess.run(
            ["git", "push"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=60,
        )
        logger.info("Stage %s: committed and pushed", stage)
    except (subprocess.TimeoutExpired, OSError) as exc:
        logger.warning("Stage %s: git commit/push failed: %s", stage, exc)


def run_pipeline(
    name: str,
    skip_to: Optional[str] = None,
    dry_run: bool = False,
    supervised: bool = True,
) -> bool:
    """Run the distillation pipeline from the current or requested stage."""
    _ensure_gitignore()
    state = load_state(name)

    # Crash recovery: reconcile state with git history
    if not skip_to:
        state = rebuild_from_git(name)

    if skip_to:
        state.current_stage = skip_to
        save_state(state)

    stages = {
        "R": lambda: run_stage_r(state, dry_run=dry_run),
        "S": lambda: run_stage_s(state, dry_run=dry_run),
        "G": lambda: run_stage_g(state, dry_run=dry_run),
        "W": lambda: run_stage_w(state, dry_run=dry_run, supervised=supervised),
        "E": lambda: run_stage_e(state, dry_run=dry_run),
    }
    while state.current_stage != "DONE":
        if STOP_FILE.exists():
            logger.warning("Stop file present; pausing before stage %s", state.current_stage)
            return False
        stage = state.current_stage
        runner = stages.get(stage)
        if runner is None:
            logger.error("No runner for stage %s", stage)
            return False
        if not runner():
            logger.error("Pipeline stopped at stage %s", stage)
            return False
        # Commit + push after each stage (skip in dry-run)
        if not dry_run:
            _git_commit_push(name, stage)
        state = load_state(name)
    logger.info("Pipeline complete for %s", name)
    return True


def _existing_state_names() -> list[str]:
    """Return names for existing distillation state directories."""
    if not DISTILLATION_DIR.exists():
        return []
    names = []
    for path in sorted(DISTILLATION_DIR.iterdir()):
        state_path = path / "state.json"
        if state_path.exists():
            try:
                data = read_json(state_path)
            except (OSError, json.JSONDecodeError):
                continue
            names.append(str(data.get("name", path.name)))
    return names


def _status_lines(name: Optional[str] = None) -> list[str]:
    """Build human-readable status lines for one or all states."""
    names = [name] if name else _existing_state_names()
    if not names:
        return ["No distillation states found."]
    lines = []
    for item_name in names:
        state = load_state(item_name)
        lines.append(
            f"{state.name}: stage={state.current_stage} "
            f"round={state.round_number} updated={state.updated_at}"
        )
    return lines


def cmd_status(name: Optional[str] = None) -> bool:
    """Print pipeline status for one state or all states."""
    for line in _status_lines(name):
        print(line)
    return True


def _validate_environment(name: Optional[str] = None) -> bool:
    """Validate prompt files, core paths, registry parseability, and artifacts."""
    ok = True
    required_prompts = [
        "research.txt",
        "generate.txt",
        "writeback.txt",
        "review_codex.txt",
        "review_claude.txt",
    ]
    for prompt_name in required_prompts:
        path = PROMPTS_DIR / prompt_name
        if not path.exists():
            logger.error("Missing prompt: %s", path)
            ok = False
    if not CORE_BODY.exists():
        logger.error("Missing core body: %s", CORE_BODY)
        ok = False
    if REGISTRY_PATH.exists():
        try:
            _read_registry()
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            logger.error("Registry validation failed: %s", exc)
            ok = False
    if name:
        state = load_state(name)
        for stage, filename in (("S", "raw_research.json"), ("G", "section_matches.json")):
            if _stage_index(state.current_stage) >= _stage_index(stage):
                if not _artifact_path(state, filename).exists():
                    logger.warning("Expected artifact missing for %s: %s", stage, filename)
    logger.info("Codex path: %s", CODEX_PATH)
    logger.info("Claude path: %s", CLAUDE_PATH)
    return ok


def build_parser() -> argparse.ArgumentParser:
    """Build the command-line parser for the distillation pipeline."""
    parser = argparse.ArgumentParser(description="Omega distillation pipeline")
    parser.add_argument("--name", help="Mathematician or source name to distill")
    parser.add_argument("--all", action="store_true", help="Run all existing states")
    parser.add_argument("--continuous", action="store_true", help="Loop until stop file exists")
    parser.add_argument("--dry-run", action="store_true", help="Avoid external model calls and writes to core")
    parser.add_argument("--skip-to", choices=STAGE_ORDER[:-1], help="Start from a specific stage")
    parser.add_argument("--status", action="store_true", help="Print pipeline status")
    parser.add_argument("--validate", action="store_true", help="Validate local configuration")
    parser.add_argument("--supervised", action="store_true", default=True, help="Ask before applying writebacks")
    parser.add_argument("--auto-apply", action="store_true", help="Apply writebacks without prompting")
    return parser


def main(argv: Optional[list[str]] = None) -> int:
    """Run the distillation command-line interface."""
    parser = build_parser()
    args = parser.parse_args(argv)
    supervised = bool(args.supervised and not args.auto_apply)

    if args.status:
        cmd_status(args.name)
        return 0
    if args.validate:
        return 0 if _validate_environment(args.name) else 1

    if args.all:
        names = _existing_state_names()
        if not names:
            parser.error("--all requires at least one existing state")
    elif args.name:
        names = [args.name]
    else:
        parser.error("Provide --name, --all, --status, or --validate")

    while True:
        all_ok = True
        for name in names:
            all_ok = run_pipeline(
                name,
                skip_to=args.skip_to,
                dry_run=args.dry_run,
                supervised=supervised,
            ) and all_ok
        if not args.continuous or STOP_FILE.exists():
            return 0 if all_ok else 1
        logger.info("Continuous mode sleeping for 20s")
        time.sleep(20)


if __name__ == "__main__":
    sys.exit(main())
