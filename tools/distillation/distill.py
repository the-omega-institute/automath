#!/usr/bin/env python3
"""Distillation pipeline for routing external mathematical methods into Omega."""

import argparse
import hashlib
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import time
from contextlib import contextmanager
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
DISTILLATION_MEMORY_PATH = BACKFLOW_DIR / "distillation_memory.json"
BOARD_STATUS_LABELS = {
    "active": "进行中",
    "open": "开放",
    "partial": "部分完成",
    "integrated": "已纳入",
    "done": "完成",
}
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
MANUAL_RESULT_ORDINAL_RE = re.compile(
    "(?i:(?:Result|" + "\u7ed3\u679c" + r")\s*[0-9]+)"
    r"|" + "\u6df1\u5316\u5e8f\u53f7" + r"\s*[:=：]?\s*[0-9]+"
    r"|(?i:\b(?:deepening|continuation)\s*(?:index|number|no\.?)?\s*[:=]?\s*[0-9]+)"
    r"|[A-Z]{2,}(?:-[A-Z]{2,})+-[0-9]+"
    r"|\\mathsf\{nr\}\s*=\s*[0-9]+"
    r"|(?i:\bnr\s*=\s*[0-9]+)",
)
SECTIONING_COMMAND_RE = re.compile(
    r"\\(?:part|chapter|section|subsection|subsubsection|paragraph|subparagraph)\*?\{"
)
CJK_RE = re.compile(r"[\u3400-\u9fff]")
KILLO_GOLDEN_TRACE_RE = re.compile(
    r"(?:"
    r"\u65b0\u589e|\u672c\u6b21|\u672c\u8f6e|\u4e0a\u4e00\u8f6e|"
    r"\u4fee\u6539\u8bb0\u5f55|\u52a0\u5165\u5982\u4e0b|"
    r"(?:\u7ed3\u8bba|\u95ed\u73af|\u8865\u5145)\s*"
    r"(?:[A-Z]|[0-9]+|[一二三四五六七八九十]+)\s*(?=[\]\}:：]|$)|"
    r"\b20[0-9]{2}[-/][0-9]{1,2}[-/][0-9]{1,2}\b"
    r")"
)
PIPELINE_METADATA_RE = re.compile(
    r"(?i:"
    r"\\textbf\{[^}]*?(?:dependency\s+status|date[- ]?time|"
    r"distillation\s+timestamp|family\s*:)[^}]*\}"
    r"|(?:dependency\s+status|date[- ]?time|distillation\s+timestamp)\s*:"
    r")"
    r"|\\textbf\{[^}]*?(?:\u4f9d\u8d56\u72b6\u6001|"
    r"\u65e5\u671f\u65f6\u95f4|\u7ed3\u679c\s*[0-9]+)[^}]*\}"
)

STAGE_ORDER = ["R", "S", "G", "W", "E", "DONE"]

# Review gate configuration
SCORE_PASS_THRESHOLD = 7
MAX_W_ROUNDS = 8          # max writeback generation + review rounds
MAX_DEEP_ROUNDS = 2       # max A-DEEP style escalation rounds per W cycle
MIN_NEW_CLAIMS = 1        # anti-fake: minimum new theorem/lemma/etc labels
MIN_CONTENT_DELTA = 200   # anti-fake: minimum chars of new claim content
WRITEBACK_LINE_LIMIT = 600
WRITEBACK_TARGET_LINE_HEADROOM = 220
MAX_WRITEBACK_TARGET_FILES = 6
PYTHON_SCAN_MATCH_THRESHOLD = 0.15
SEMANTIC_SCAN_CANDIDATES = 12
SEMANTIC_SCAN_CONTEXT_CHARS = 4500
SEMANTIC_SCAN_ACCEPT_THRESHOLD = 0.55
GLOBAL_EVIDENCE_MAX_CLAIMS = 80
GLOBAL_EVIDENCE_MAX_INTERFACES = 50
ORACLE_EVIDENCE_MAX_SECTION_INDEX = 3
ORACLE_EVIDENCE_MAX_CLAIMS = 2
ORACLE_EVIDENCE_MAX_EXISTING = 2
ORACLE_EVIDENCE_MAX_INTERFACES = 2
ORACLE_EVIDENCE_MAX_MEMORY = 2
ORACLE_SECTION_CONTEXT_CHARS = 40000
ORACLE_DEEPENING_SECTION_CONTEXT_CHARS = int(
    os.environ.get("ORACLE_DEEPENING_SECTION_CONTEXT_CHARS", "1000")
)
GLOBAL_EVIDENCE_SNIPPET_CHARS = 900
ORACLE_EVIDENCE_SNIPPET_CHARS = int(os.environ.get("ORACLE_EVIDENCE_SNIPPET_CHARS", "160"))
POLICY_VERSION = 1
ORACLE_SERVER = "http://127.0.0.1:8765"
ORACLE_SERVER_SCRIPT = REPO_ROOT / "tools" / "chatgpt-oracle" / "oracle_server.py"
ORACLE_DONE_DIR = REPO_ROOT / "tools" / "chatgpt-oracle" / "oracle" / "done"
DEFAULT_ORACLE_MODEL = "chatgpt-5.4-pro-extended"
DEFAULT_ORACLE_TIMEOUT = 7200
ORACLE_CLAIM_TIMEOUT = int(os.environ.get("ORACLE_CLAIM_TIMEOUT", "90"))
ORACLE_AGENT_STALE_TIMEOUT = int(os.environ.get("ORACLE_AGENT_STALE_TIMEOUT", "300"))
CODEX_INFRA_RETRIES = int(os.environ.get("DISTILL_CODEX_INFRA_RETRIES", "3"))
CODEX_INFRA_RETRY_SLEEP = int(os.environ.get("DISTILL_CODEX_INFRA_RETRY_SLEEP", "20"))
REVIEW_BACKENDS = ("codex", "codex-claude", "claude")
DEFAULT_REVIEW_BACKEND = os.environ.get("DISTILL_REVIEW_BACKEND", "claude")
if DEFAULT_REVIEW_BACKEND not in REVIEW_BACKENDS:
    DEFAULT_REVIEW_BACKEND = "claude"

LOG_DIR.mkdir(parents=True, exist_ok=True)
logger = logging.getLogger("distill")
logger.setLevel(logging.INFO)

CODEX_INFRA_UNAVAILABLE_MARKERS = (
    "selected model is at capacity",
    "please try a different model",
    "rate limit",
    "try again later",
    "timed out",
    "(timeout)",
    "(start-failed)",
    "(codex-exec-failed",
)
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


def _path_exists(path: Path) -> bool:
    """Return whether a path exists, treating inaccessible paths as absent."""
    try:
        return path.exists()
    except OSError as exc:
        logger.debug("Skipping inaccessible path probe %s: %s", path, exc)
        return False


def _path_is_executable(path: Path) -> bool:
    """Return whether a candidate CLI path is present and executable."""
    return _path_exists(path) and os.access(str(path), os.R_OK | os.X_OK)


def _make_temporary_directory(prefix: str = "omega_distill_") -> Path:
    """Create a writable temporary directory without restrictive Windows ACLs."""
    base = Path(os.environ.get("DISTILL_TEMP_DIR", DISTILLATION_DIR / "tmp"))
    base.mkdir(parents=True, exist_ok=True)
    for attempt in range(100):
        name = f"{prefix}{os.getpid()}_{time.time_ns()}_{attempt}"
        path = base / name
        try:
            path.mkdir()
            break
        except FileExistsError:
            continue
    else:
        raise FileExistsError(f"Could not create temporary directory under {base}")
    return path


@contextmanager
def _temporary_directory(prefix: str = "omega_distill_"):
    """Context manager for writable temporary directories."""
    path = _make_temporary_directory(prefix)
    try:
        yield str(path)
    finally:
        shutil.rmtree(path, ignore_errors=True)


def _find_codex() -> str:
    """Find the Codex CLI, including npm and Homebrew fallback locations."""
    found = shutil.which("codex")
    if found:
        return found
    if sys.platform == "win32":
        npm_codex = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if _path_is_executable(npm_codex):
            return str(npm_codex)
    elif sys.platform == "darwin":
        for candidate in ("/opt/homebrew/bin/codex", "/usr/local/bin/codex"):
            if _path_is_executable(Path(candidate)):
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

    codex_bin = CODEX_PATH if _path_is_executable(Path(CODEX_PATH)) else shutil.which("codex")
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
        temp_dir = _make_temporary_directory(prefix="omega_distill_codex_")
        prompt_file = temp_dir / "prompt.txt"
        out_file = temp_dir / "output.txt"
        stdout_file = temp_dir / "stdout.jsonl"
        stderr_file = temp_dir / "stderr.txt"

    write_text(prompt_file, prompt)
    write_text(out_file, "")

    cmd = [
        str(codex_bin),
        "exec",
        "--sandbox",
        "read-only",
        "--json",
        "-C",
        str(target_dir),
        "-o",
        str(out_file),
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    use_shell = IS_WINDOWS and str(codex_bin).lower().endswith(".cmd")
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

    if returncode != 0:
        details = _jsonl_agent_messages(stdout) or stderr or stdout
        if temp_dir is not None:
            shutil.rmtree(temp_dir, ignore_errors=True)
        return f"(codex-exec-failed rc={returncode})\n{details[:2000]}"

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


def _is_codex_infra_unavailable(response: str) -> bool:
    """Return true for transient Codex infrastructure failures."""
    lower = (response or "").lower()
    return any(marker in lower for marker in CODEX_INFRA_UNAVAILABLE_MARKERS)


def _codex_exec_with_infra_retries(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 1800,
    model: Optional[str] = None,
    dry_run: bool = False,
    log_tag: Optional[str] = None,
) -> str:
    """Run Codex with retries that do not consume mathematical attempts."""
    attempts = max(1, CODEX_INFRA_RETRIES)
    last_response = ""
    for infra_attempt in range(1, attempts + 1):
        tagged = (
            log_tag
            if infra_attempt == 1 or not log_tag
            else f"{log_tag}_infra{infra_attempt}"
        )
        last_response = codex_exec(
            prompt,
            work_dir=work_dir,
            timeout_seconds=timeout_seconds,
            model=model,
            dry_run=dry_run,
            log_tag=tagged,
        )
        if not _is_codex_infra_unavailable(last_response):
            return last_response
        if infra_attempt < attempts:
            logger.warning(
                "Codex infrastructure unavailable; retrying %d/%d after %ss",
                infra_attempt + 1,
                attempts,
                CODEX_INFRA_RETRY_SLEEP,
            )
            time.sleep(max(0, CODEX_INFRA_RETRY_SLEEP))
    return last_response


def _find_claude() -> str:
    """Find the Claude CLI, including npm and Homebrew fallback locations."""
    found = shutil.which("claude")
    if found:
        return found
    if sys.platform == "win32":
        npm_claude = Path.home() / "AppData" / "Roaming" / "npm" / "claude.cmd"
        if _path_is_executable(npm_claude):
            return str(npm_claude)
    elif sys.platform == "darwin":
        for candidate in ("/opt/homebrew/bin/claude", "/usr/local/bin/claude"):
            if _path_is_executable(Path(candidate)):
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
    if not _path_is_executable(Path(claude_bin)) and not shutil.which(claude_bin):
        logger.warning("Claude CLI not found; falling back to codex_exec")
        return _codex_exec_with_infra_retries(prompt, work_dir=target_dir, dry_run=dry_run)

    cmd = [str(claude_bin), "-p", "--dangerously-skip-permissions"]
    use_shell = IS_WINDOWS and str(claude_bin).lower().endswith(".cmd")
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
            return _codex_exec_with_infra_retries(prompt, work_dir=target_dir, dry_run=dry_run)
    return output


def _load_prompt(name: str) -> str:
    """Load a prompt template from the publication prompts directory."""
    prompt_name = name if name.endswith(".txt") else f"{name}.txt"
    return read_text(PROMPTS_DIR / prompt_name)


def _deep_research_directive() -> str:
    """Load the shared deep-research directive used by scan and deepening."""
    return _load_prompt("deep_research_directive")


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


def _escape_json_string_control_chars(text: str) -> str:
    """Escape raw control characters that appear inside JSON strings."""
    out: list[str] = []
    in_string = False
    escape = False
    for char in text:
        if in_string:
            if escape:
                out.append(char)
                escape = False
                continue
            if char == "\\":
                out.append(char)
                escape = True
                continue
            if char == '"':
                out.append(char)
                in_string = False
                continue
            if char == "\n":
                out.append("\\n")
                continue
            if char == "\r":
                out.append("\\r")
                continue
            if char == "\t":
                out.append("\\t")
                continue
            out.append(char)
            continue
        out.append(char)
        if char == '"':
            in_string = True
    return "".join(out)


def _parse_json_candidate(candidate: str) -> Any:
    """Parse a balanced JSON candidate with LaTeX/control-char repairs."""
    variants = [
        candidate,
        _repair_latex_escapes(candidate),
    ]
    variants.extend(_escape_json_string_control_chars(item) for item in list(variants))
    seen: set[str] = set()
    last_error: Optional[json.JSONDecodeError] = None
    for variant in variants:
        if variant in seen:
            continue
        seen.add(variant)
        try:
            return json.loads(variant)
        except json.JSONDecodeError as exc:
            last_error = exc
    if last_error is not None:
        raise last_error
    raise json.JSONDecodeError("empty JSON candidate", candidate, 0)


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
    first_json_start: Optional[int] = None
    for index, char in enumerate(text):
        if char in "{[":
            first_json_start = index
            break
        if not char.isspace():
            break
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
                        return _parse_json_candidate(candidate)
                    except json.JSONDecodeError:
                        if start == first_json_start and first_char == "[":
                            return None
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

    root_path = REPO_ROOT / ".gitignore"
    root_lines = read_text(root_path).splitlines() if root_path.exists() else []
    root_ignores = [
        "papers/publication/backflow/.distillation/",
        "tools/distillation/.pipeline.stop",
    ]
    changed = False
    for item in root_ignores:
        if item not in root_lines:
            root_lines.append(item)
            changed = True
    if changed:
        write_text(root_path, "\n".join(root_lines).strip() + "\n")


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
    # Local-only policy model.  These fields live under .distillation/ and are
    # deliberately excluded from the public commit surface.
    scope_contract: dict[str, Any] = field(default_factory=dict)
    policy_state: dict[str, Any] = field(default_factory=dict)
    open_debts: list[dict[str, Any]] = field(default_factory=list)
    split_candidates: list[dict[str, Any]] = field(default_factory=list)
    blocked: dict[str, Any] = field(default_factory=dict)


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
        scope_contract=dict(data.get("scope_contract") or {}),
        policy_state=dict(data.get("policy_state") or {}),
        open_debts=list(data.get("open_debts") or []),
        split_candidates=list(data.get("split_candidates") or []),
        blocked=dict(data.get("blocked") or {}),
    )


def _write_artifact_json(state: DistillState, filename: str, data: Any) -> None:
    """Write a state-local JSON artifact."""
    write_json(_artifact_path(state, filename), data)


def _read_artifact_json(state: DistillState, filename: str) -> Any:
    """Read a state-local JSON artifact."""
    return read_json(_artifact_path(state, filename))


def _artifact_exists(state: DistillState, filename: str) -> bool:
    """Return whether a state-local artifact exists."""
    return _artifact_path(state, filename).exists()


def _remove_artifact_if_exists(state: DistillState, filename: str) -> None:
    """Remove a stale state-local artifact if it exists."""
    path = _artifact_path(state, filename)
    if path.exists():
        path.unlink()


def _remove_artifacts_if_exists(state: DistillState, filenames: list[str]) -> None:
    """Remove stale state-local artifacts and log the cleanup."""
    removed = []
    for filename in filenames:
        path = _artifact_path(state, filename)
        if path.exists():
            path.unlink()
            removed.append(filename)
    if removed:
        logger.info("Invalidated stale artifacts for %s: %s", state.name, ", ".join(removed))


def _read_artifact_json_or_none(state: DistillState, filename: str) -> Any:
    """Read a state-local JSON artifact, returning None when unavailable."""
    path = _artifact_path(state, filename)
    if not path.exists():
        return None
    try:
        return read_json(path)
    except (OSError, json.JSONDecodeError) as exc:
        logger.warning("Could not read artifact %s: %s", path, exc)
        return None


def _oracle_server_status() -> dict[str, Any]:
    """Return the local ChatGPT Oracle bridge status, or {} if unreachable."""
    import urllib.error
    import urllib.request

    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER}/status", timeout=5) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        return data if isinstance(data, dict) else {}
    except (OSError, urllib.error.URLError, json.JSONDecodeError):
        return {}


def _ensure_oracle_server_running() -> dict[str, Any]:
    """Return Oracle status, starting the local bridge if it is offline."""
    status = _oracle_server_status()
    if status:
        return status
    if not ORACLE_SERVER_SCRIPT.exists():
        logger.warning("ChatGPT Oracle server script not found: %s", ORACLE_SERVER_SCRIPT)
        return {}

    oracle_log_dir = LOG_DIR / "oracle"
    oracle_log_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = oracle_log_dir / "oracle_server_stdout.log"
    stderr_path = oracle_log_dir / "oracle_server_stderr.log"
    try:
        with open(stdout_path, "ab") as stdout, open(stderr_path, "ab") as stderr:
            subprocess.Popen(
                [sys.executable, str(ORACLE_SERVER_SCRIPT)],
                cwd=str(REPO_ROOT),
                stdout=stdout,
                stderr=stderr,
                stdin=subprocess.DEVNULL,
                creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if IS_WINDOWS else 0,
            )
    except OSError as exc:
        logger.warning("Could not start ChatGPT Oracle server: %s", exc)
        return {}

    for _ in range(10):
        time.sleep(1)
        status = _oracle_server_status()
        if status:
            logger.info("Started ChatGPT Oracle server at %s", ORACLE_SERVER)
            return status
    logger.warning("ChatGPT Oracle server did not become ready at %s", ORACLE_SERVER)
    return {}


def _oracle_cancel_task(task_id: str, reason: str) -> None:
    """Best-effort cancel for queued/unclaimed Oracle tasks."""
    import urllib.error
    import urllib.request

    try:
        req = urllib.request.Request(
            f"{ORACLE_SERVER}/cancel",
            data=json.dumps({"task_id": task_id, "reason": reason}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        urllib.request.urlopen(req, timeout=10).read()
    except (OSError, urllib.error.URLError):
        return


def _oracle_claimed_agent_infos(
    status: dict[str, Any],
    task_id: str,
) -> list[tuple[str, dict[str, Any]]]:
    """Return browser-agent status rows currently assigned to an Oracle task."""
    agents = status.get("agents", {}) if isinstance(status, dict) else {}
    if not isinstance(agents, dict):
        return []
    claimed: list[tuple[str, dict[str, Any]]] = []
    for agent_id, info in agents.items():
        if isinstance(info, dict) and info.get("task_id") == task_id:
            claimed.append((str(agent_id), info))
    return claimed


def _oracle_stale_agent_claims(
    status: dict[str, Any],
    task_id: str,
    stale_timeout: int = ORACLE_AGENT_STALE_TIMEOUT,
) -> list[tuple[str, dict[str, Any]]]:
    """Return claimed Oracle agents whose heartbeat age exceeds stale_timeout."""
    stale: list[tuple[str, dict[str, Any]]] = []
    for agent_id, info in _oracle_claimed_agent_infos(status, task_id):
        try:
            age = int(info.get("elapsed", 0))
        except (TypeError, ValueError):
            age = 0
        if age >= stale_timeout:
            stale.append((agent_id, info))
    return stale


_ORACLE_METADATA_RE = re.compile(r"^\s*<!--\s*oracle metadata:\s*.*?-->\s*", re.DOTALL)


def _strip_oracle_response_metadata(text: str) -> str:
    """Remove local oracle metadata comments from persisted browser responses."""
    return _ORACLE_METADATA_RE.sub("", text or "", count=1).lstrip()


def _read_oracle_done_response(task_id: str) -> str:
    """Read a durable browser result from tools/chatgpt-oracle/oracle/done."""
    if not task_id:
        return ""
    path = ORACLE_DONE_DIR / f"{task_id}.md"
    if not path.exists():
        return ""
    try:
        return _strip_oracle_response_metadata(read_text(path)).strip()
    except OSError:
        return ""


def chatgpt_oracle_exec(
    state: DistillState,
    prompt: str,
    *,
    log_tag: str,
    timeout_seconds: int = DEFAULT_ORACLE_TIMEOUT,
    model: str = DEFAULT_ORACLE_MODEL,
    pdf_path: Optional[Path] = None,
    dry_run: bool = False,
) -> str:
    """Submit a prompt to the local ChatGPT Oracle bridge and wait for a result."""
    if dry_run:
        logger.info(
            "[DRY RUN] ChatGPT Oracle task=%s model=%s prompt=%s",
            log_tag,
            model,
            prompt[:300].replace("\n", " "),
        )
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        write_text(_artifact_path(state, f"{log_tag}_oracle_prompt_{ts}.txt"), prompt)
        return ""

    import base64
    import urllib.error
    import urllib.request

    status_before = _ensure_oracle_server_running()
    if not status_before:
        logger.warning(
            "ChatGPT Oracle server unreachable at %s; start tools/chatgpt-oracle/oracle_server.py",
            ORACLE_SERVER,
        )
        return ""
    logger.info(
        "ChatGPT Oracle status: queue=%s agents=%s/%s completed=%s",
        status_before.get("queue_length", "?"),
        status_before.get("agents_busy", "?"),
        status_before.get("max_agents", "?"),
        status_before.get("completed", "?"),
    )

    task_id = f"{_slugify(state.name)}_{log_tag}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    payload: dict[str, Any] = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
    }
    if pdf_path:
        path = Path(pdf_path)
        if path.exists():
            payload["pdf_base64"] = base64.b64encode(path.read_bytes()).decode("ascii")
            payload["pdf_name"] = path.name
        else:
            logger.warning("Oracle PDF path does not exist: %s", path)

    try:
        req = urllib.request.Request(
            f"{ORACLE_SERVER}/submit",
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        urllib.request.urlopen(req, timeout=30).read()
    except (OSError, urllib.error.URLError) as exc:
        logger.warning("ChatGPT Oracle submit failed: %s", exc)
        return ""

    logger.info(
        "ChatGPT Oracle task queued: %s (timeout=%ss, model=%s)",
        task_id,
        timeout_seconds,
        model,
    )

    def persist_response(response: str, source: str) -> str:
        metadata = {
            "task_id": task_id,
            "model": model,
            "timestamp": _now_iso(),
            "prompt_length": len(prompt),
            "response_length": len(response),
            "pdf_path": str(pdf_path) if pdf_path else "",
            "oracle_status_before": status_before,
            "oracle_status_after": _oracle_server_status(),
            "source": source,
        }
        write_text(
            _artifact_path(state, f"{log_tag}_oracle_response.md"),
            f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
        )
        logger.info(
            "ChatGPT Oracle response received: %s (%d chars, source=%s)",
            task_id,
            len(response),
            source,
        )
        return response

    start = time.time()
    while time.time() - start < timeout_seconds:
        try:
            with urllib.request.urlopen(f"{ORACLE_SERVER}/result/{task_id}", timeout=10) as resp:
                result = json.loads(resp.read().decode("utf-8"))
            if result.get("status") == "completed":
                response = str(result.get("response", ""))
                return persist_response(response, "server_result")
        except (OSError, urllib.error.URLError, json.JSONDecodeError):
            pass

        done_response = _read_oracle_done_response(task_id)
        if done_response:
            return persist_response(done_response, "done_file")

        elapsed = int(time.time() - start)
        status = _oracle_server_status()
        claimed_infos = _oracle_claimed_agent_infos(status, task_id)
        claimed_by = [agent_id for agent_id, _ in claimed_infos]
        if not claimed_by and elapsed >= ORACLE_CLAIM_TIMEOUT:
            _oracle_cancel_task(task_id, "claim_timeout_no_foreground_agent")
            logger.warning(
                "ChatGPT Oracle task not claimed after %ss; continuing without Oracle: %s",
                ORACLE_CLAIM_TIMEOUT,
                task_id,
            )
            return ""
        stale_claims = _oracle_stale_agent_claims(status, task_id)
        if claimed_by and stale_claims and len(stale_claims) == len(claimed_infos):
            stale_detail = ", ".join(
                f"{agent_id}:phase={info.get('phase', '?')}:elapsed={info.get('elapsed', '?')}s"
                for agent_id, info in stale_claims
            )
            _oracle_cancel_task(task_id, "stale_browser_agent")
            logger.warning(
                "ChatGPT Oracle task claimed by stale browser agent(s) after %ss; "
                "continuing without Oracle: %s (%s)",
                ORACLE_AGENT_STALE_TIMEOUT,
                task_id,
                stale_detail,
            )
            return ""
        if elapsed > 0 and elapsed % 60 == 0:
            logger.info("Waiting for ChatGPT Oracle task %s (%ss)", task_id, elapsed)
        time.sleep(30)

    logger.warning("ChatGPT Oracle task timed out: %s", task_id)
    return ""


def _unique_strings(items: Any) -> list[str]:
    """Return stable, non-empty strings from a mixed iterable."""
    result = []
    if not isinstance(items, list):
        return result
    for item in items:
        value = str(item).strip()
        if value and value not in result:
            result.append(value)
    return result


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
        "bad_example_mechanisms": [
            {
                "name": "mechanism name",
                "worst_counterexample_shape": "minimal failure object",
                "classification_skeletons": ["sticky|Frostman failure|slab|holonomy|budget"],
                "closure_route": "how the skeleton can be defeated or closed",
            }
        ],
        "frontier_interfaces": [
            {
                "omega_interface": "concrete Omega interface or label family",
                "source_tool": "source-side method/tool",
                "publishable_question": "new result to attempt",
                "risk": "duplication or overclaim risk",
            }
        ],
        "novelty_guardrails": [
            "specific old-result shell or standard theorem that must not be repackaged"
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
        "frontier_chains": [
            {
                "name": "publishable theorem-chain frontier",
                "target_sections": ["core section slug"],
                "result_chain": ["definition", "theorem", "corollary"],
                "closure_route": "route to proof or obstruction",
                "status": "active",
            }
        ],
        "coverage_debts": [
            {
                "family": "theorem family name",
                "missing_mechanism": "what remains unclosed",
                "target_sections": ["core section slug"],
                "reason": "why this is still a debt",
            }
        ],
        "closure_criteria": [
            "concrete condition that must hold before the source is considered closed"
        ],
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


def _oracle_deepening_schema() -> str:
    """Return the ChatGPT Oracle deepening context schema."""
    schema = {
        "status": "ok|blocked|partial",
        "current_datetime": "ISO timestamp emitted by the Oracle",
        "focused_family": "theorem family name",
        "numbering_continuation": "how the next result numbers should continue",
        "main_theorem_chain": [
            {
                "type": "definition|theorem|proposition|corollary|conjecture",
                "proposed_title": "precise paper-ready title",
                "target_sections": ["core section slug"],
                "omega_objects": ["specific Omega definitions/labels/constructs"],
                "minimal_hypotheses": ["explicit local assumptions"],
                "conclusion": "nontrivial project-bound conclusion",
                "proof_spine": [
                    "worst counterexample",
                    "classified skeleton",
                    "structure/decomposition/budget step",
                    "closure or obstruction"
                ],
                "novelty_reason": "why this is not a known theorem restatement or old writeback",
                "risk_to_avoid": "main overclaim or unsupported dependency",
            }
        ],
        "bad_example_classification": [
            {
                "mechanism": "sticky|Frostman failure|slab/sector collapse|holonomy|infinite externalization",
                "classification_statement": "formal structure statement to target",
                "closing_move": "proof move that can close the mechanism",
            }
        ],
        "local_to_global_obstructions": [
            {
                "local_object": "locally valid object",
                "global_failure": "why it cannot glue globally",
                "certificate": "holonomy/curvature/boundary/WalshStokes/Euler/budget certificate",
            }
        ],
        "forbidden_repetitions": ["labels, claims, or strategies not to repeat"],
        "codex_writeback_instructions": [
            "specific instruction for the next Codex writeback attempt"
        ],
        "sidecar_candidates": [
            {
                "title": "compact name for a useful side result not needed by the focused family",
                "target_sections": ["future core section slug"],
                "scope_relation": "off_scope|future_split|supporting_context",
                "source_reason": "why this arose while pushing the focused family",
                "reuse_guidance": "how a later agent should load or avoid this context",
                "status": "open",
            }
        ],
    }
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


def _semantic_scan_schema() -> str:
    """Return the Stage S+ semantic scan output schema."""
    schema = {
        "semantic_matches": [
            {
                "section": "core section slug",
                "tex_file": "relative path under theory sections/body",
                "semantic_score": 0.0,
                "mechanism": "bad-example mechanism exposed in this section",
                "theorem_chain_role": "how this section can support a publishable chain",
                "reason": "short evidence-bound justification",
                "required_context_labels": ["nearby label or construction"],
            }
        ],
        "frontier_chains": [
            {
                "name": "unified theorem-chain name",
                "target_sections": ["core section slug"],
                "result_chain": ["definition/theorem/corollary sequence to attempt"],
                "closure_route": "how this chain could close or fail",
                "novelty_risk": "what would make it duplicate old material",
            }
        ],
        "rejects": [
            {
                "section": "core section slug",
                "reason": "why vocabulary match is not a real theorem-chain target",
            }
        ],
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
    lines = ["PRIOR FEEDBACK (address ALL of these):"]
    has_feedback = False
    for entry in state.prior_feedback[-8:]:
        lines.append(f"  - {entry}")
        has_feedback = True
    blocked = _read_artifact_json_or_none(state, "blocked.json")
    if isinstance(blocked, dict) and blocked.get("status") == "review_failed":
        blocked_summary = _compact_review_feedback(blocked.get("last_review", {}))
        if blocked_summary:
            recent_feedback = "\n".join(state.prior_feedback[-8:])
            if blocked_summary not in recent_feedback:
                lines.append(f"  - Last blocked review: {blocked_summary}")
                has_feedback = True
    if state.scores:
        score_lines = []
        for stage_key, review_data in state.scores.items():
            if isinstance(review_data, dict):
                codex_s = review_data.get("codex", {}).get("score", "?")
                secondary_key = "oracle" if "oracle" in review_data else "claude"
                secondary_s = review_data.get(secondary_key, {}).get("score", "?")
                passed = review_data.get("gate_passed", "?")
                score_lines.append(
                    f"{stage_key}: codex={codex_s} {secondary_key}={secondary_s} pass={passed}"
                )
        if score_lines:
            lines.append("Score history: " + ", ".join(score_lines[-4:]))
            has_feedback = True
    if not has_feedback:
        return ""
    return "\n".join(lines)


def _family_specific_deepening_contract(focused_family: Optional[dict[str, Any]]) -> str:
    """Return narrow last-mile guidance for families with known failure modes."""
    if not focused_family:
        return ""
    family_slug = _slugify(str(focused_family.get("name", "")))
    if family_slug == "random_sparse_obstruction_families":
        return "\n".join(
            [
                "FAMILY-SPECIFIC LAST-MILE CONTRACT:",
                "- This family has repeatedly failed when generic finite-dimensional",
                "  linear algebra, graph cohomology, or abstract ledger perturbations",
                "  were stated as Omega reconstruction obstructions. Output at most",
                "  1-2 conservative writebacks, and omit any target whose local",
                "  Omega carrier is not fully defined in the supplied context.",
                "- Absolutely do not include the visible style tokens 新增, 本次,",
                "  本轮, 上一轮, 修改记录, 加入如下, 补充 A, 结论 1, or 闭环 1",
                "  anywhere in a title, statement, proof, or explanatory sentence.",
                "- For statistical_stability, quantify explicitly over all probability",
                "  measures on the concrete finite-resolution carrier X_m or its",
                "  locally named image, and bind the sparse residual predicate to the",
                "  surrounding finite-resolution congruence/sieve objects. Do not",
                "  call a witness empirical unless rational/integer multiplicities",
                "  are proved.",
                "- For group_unification, use only a formal cycle-circulation or",
                "  holonomy-audit statement unless the graph, oriented edges, and edge",
                "  ledger are constructed from actual window-6/foldbin transition data",
                "  in the snippet. Do not use filling-cost, expansion-budget, or",
                "  reconstruction-obstruction language unless those objects are defined",
                "  and the claimed implication is proved. Avoid mixed-language phrases",
                "  such as admit.",
                "- For zeta_finite_part, prefer a short corollary/audit lemma of the",
                "  existing denominator-ledger and Euler-tail results. Locally define",
                "  every symbol before use, especially K>=2, M=M_\\theta,",
                "  \\lambda=\\lambda(\\theta), d=\\dim M, and \\mathcal E_K. Do not claim",
                "  an abstract ledger perturbation is realizable by an Euler matrix",
                "  family unless the realization hypothesis is explicitly added.",
                "- For POM, include Hankel or projection-word readings only if they are",
                "  explicitly included in the stated finite test space. State the basis",
                "  and normalization convention for any support-size bound.",
                "- Prefer a shorter accepted lemma/corollary over broad coverage of all",
                "  target sections. The zeta target may be near the line budget; omit it",
                "  if the result cannot be made short and locally anchored.",
            ]
        )
    if family_slug == "holonomy_residue_classification":
        return "\n".join(
            [
                "FAMILY-SPECIFIC LAST-MILE CONTRACT:",
                "- This family has repeatedly failed on overstated H_1 and holonomy",
                "  claims. Output at most 1-2 short writebacks, and prefer a single",
                "  accepted corollary over broad multi-section coverage.",
                "- Never claim that a finite nerve automatically has free H_1. In",
                "  degree 1, use the correct universal-coefficient argument, or work",
                "  with explicit 1-cycle representatives, or add an explicit torsion-",
                "  free / finite-graph hypothesis.",
                "- Cylinder or torus audit conclusions are allowed only after you",
                "  explicitly assume that the named loops generate H_1(K;\\ZZ) of the",
                "  finite protocol quotient, or after you state that all other cycle",
                "  classes are already killed by admitted face/boundary relations.",
                "- If a map \\lambda is used on loops or cycles, define it as an",
                "  additive group homomorphism on Z_1(K;\\ZZ) and state that it kills",
                "  boundaries, or equivalently descends to H_1(K;\\ZZ). Do not use",
                "  loop-indexed ledger language without that additivity hypothesis.",
                "- Do not use words like persistent or closure unless the statement",
                "  includes explicit admissible refinement maps and a stability",
                "  hypothesis. Otherwise say finite-nerve or finite-protocol holonomy",
                "  class / reduced overlap-ledger triviality.",
                "- In physical_spacetime_skeleton, anchor any writeback directly to",
                "  def:physical-spacetime-acceptable-instantiation and to the existing",
                "  reduced-holonomy tree gate. Prefer a corollary/specialization of the",
                "  registered gate over a parallel exactness theorem.",
                "- Eliminate mixed English prose in theorem bodies unless it is a fixed",
                "  object name already present in the local target context.",
                "- Any refinement family such as \\mathscr R must be explicitly defined",
                "  before use, and every special quotient/carrier symbol must be",
                "  locally introduced in the statement.",
            ]
        )
    if family_slug == "sum_product_obstruction_classification":
        return "\n".join(
            [
                "FAMILY-SPECIFIC LAST-MILE CONTRACT:",
                "- This family has repeatedly failed when ordinary finite-ring,",
                "  denominator, CRT, orbit-stabilizer, injectivity, or Kneser-style",
                "  observations were relabeled as Bourgain sum-product content.",
                "  Do not output such writebacks.",
                "- Output at most 1-2 writebacks. Prefer one locally anchored result",
                "  with a genuine growth lower bound or a genuine arithmetic",
                "  obstruction over broad target coverage.",
                "- A valid writeback must contain a nontrivial sum-product statement:",
                "  either an explicit finite-field/finite-ring growth alternative",
                "  of the form |A+A|+|A\\cdot A| >= |A|^{1+epsilon} under stated",
                "  non-subfield/non-subring hypotheses, or a structural obstruction",
                "  that uses the target's specific arithmetic carrier and proves why",
                "  simultaneous additive and multiplicative stability forces that",
                "  carrier into a named proper subring, quotient, representation",
                "  block, or denominator class.",
                "- The proof must use both addition and multiplication in an essential",
                "  way. Reject yourself if the argument would remain true after",
                "  deleting multiplication, after replacing multiplication by an",
                "  arbitrary second operation, or if it only says that a finite set",
                "  closed under ring operations generates a finite subring.",
                "- Do not target the Fibonacci congruence file unless the snippet",
                "  constructs an intrinsic local ring/finite-field projection from",
                "  the supplied context. The monoid quotient D/\\equiv \\cong \\NN is",
                "  not by itself a sum-product carrier.",
                "- In the Z_34 representation target, do not identify real rotation",
                "  planes with complex characters without handling conjugate pairs.",
                "  Tensor products of real planes must account for both i+j and i-j",
                "  escape indices, or the result must avoid character-product claims.",
                "- In the zeta/Serrin flux target, denominator clearing or factorization",
                "  through a finite residue map is not enough. The statement must use",
                "  an analytic or arithmetic property visible in the local context,",
                "  not merely the fact that rational coordinates have finite",
                "  denominators.",
                "- If no supplied target supports a genuine statement of this kind,",
                "  return a single narrow conditional lemma whose hypotheses explicitly",
                "  introduce the finite arithmetic carrier and the non-subring",
                "  condition; do not overstate it as an intrinsic Omega theorem.",
            ]
        )
    if family_slug != "worst_counterexample_exponent_bootstrapping":
        return ""
    return "\n".join(
        [
            "FAMILY-SPECIFIC LAST-MILE CONTRACT:",
            "- This family is currently failing because broad ledger/skeleton",
            "  theorems overclaim. Do not introduce a standalone five-skeleton",
            "  ledger framework, arbitrary skeleton classes, unique skeleton",
            "  compression, closed-skeleton sets, inverse-limit closure, or",
            "  K_h(d+alpha; L_h^+) closure unless every object and inheritance",
            "  condition is already visible in the target context and proved.",
            "- The primary accepted writeback should be a narrow FRT result",
            "  anchored directly to thm:frt-apparent-randomness-freezing-escort",
            "  and distill:wang_zahl-sticky_reduction_and_scale_saturated_closure-freezing-forces-sticky-or-groundstate-proliferation.",
            "- Preferred shape: a proposition/corollary proving a conditional",
            "  non-sticky ground-state carrier proliferation or exponent-budget",
            "  lower bound using only q, pi_{m,q}, A_m^{max}, gamma_{m,h},",
            "  G_{m,h}^{max}, epsilon_m, and nearby FRT notation.",
            "- If the word sticky is used, use the existing sticky/non-sticky",
            "  notion from def:distill-folding-integer-depth-sticky-test or",
            "  explicitly state a fold-aware multiscale coarse-fine occupancy",
            "  law. Never redefine sticky as a single-atom mass condition.",
            "- POM or conclusion targets are optional. Omit them unless the local",
            "  file already supplies the exact support/coefficient/holonomy",
            "  objects needed for a complete proof.",
            "- Output 1-2 writebacks, with the FRT writeback first. Prefer a",
            "  conservative theorem that passes review over broad coverage.",
        ]
    )


def _theorem_family_names(state: DistillState) -> list[str]:
    """Return theorem-family names from raw research, preserving order."""
    try:
        raw = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError:
        return []
    names = []
    for family in raw.get("theorem_families", []):
        if not isinstance(family, dict):
            continue
        name = str(family.get("name", "")).strip()
        if name and name not in names:
            names.append(name)
    return names


def _all_families_completed(state: DistillState) -> bool:
    """Return whether every known theorem family has been completed."""
    names = _theorem_family_names(state)
    if not names:
        return False
    completed = set(state.completed_families)
    return all(name in completed for name in names)


def _prune_completed_families(state: DistillState) -> bool:
    """Drop completion markers that no longer belong to the current inventory."""
    names = _theorem_family_names(state)
    if not names or not state.completed_families:
        return False
    allowed = set(names)
    before = list(state.completed_families)
    state.completed_families = [name for name in before if name in allowed]
    if before == state.completed_families:
        return False
    state.depth_cycle = min(state.depth_cycle, len(state.completed_families))
    removed = [name for name in before if name not in allowed]
    logger.warning(
        "Pruned stale completed families for %s: %s",
        state.name,
        ", ".join(removed),
    )
    return True


def _invalidate_after_stage_r(state: DistillState) -> None:
    """A new scope contract invalidates all downstream local artifacts."""
    _remove_artifacts_if_exists(
        state,
        [
            "section_matches.json",
            "global_evidence_pack.json",
            "generated_payload.json",
            "writeback_response.json",
            "writebacks.json",
            "writeback_ledger.json",
            "registry_entry.json",
            "blocked.json",
        ],
    )
    state.completed_families = []
    state.depth_cycle = 0
    state.scores = {}
    state.prior_feedback = []
    state.blocked = {}


def _invalidate_after_stage_s(state: DistillState) -> None:
    """A new router/evidence pass invalidates generated and writeback artifacts."""
    _remove_artifacts_if_exists(
        state,
        [
            "generated_payload.json",
            "writeback_response.json",
            "writebacks.json",
            "writeback_ledger.json",
            "registry_entry.json",
            "blocked.json",
        ],
    )
    state.scores = {}
    state.prior_feedback = []
    state.blocked = {}
    _prune_completed_families(state)


def _invalidate_after_stage_g(state: DistillState) -> None:
    """A new generated payload invalidates writeback and export artifacts."""
    _remove_artifacts_if_exists(
        state,
        [
            "writeback_response.json",
            "writebacks.json",
            "writeback_ledger.json",
            "registry_entry.json",
            "blocked.json",
        ],
    )
    state.scores = {}
    state.prior_feedback = []
    state.blocked = {}
    _prune_completed_families(state)


def _artifact_mtime(state: DistillState, filename: str) -> Optional[float]:
    """Return an artifact mtime, or None when it is unavailable."""
    path = _artifact_path(state, filename)
    try:
        return path.stat().st_mtime if path.exists() else None
    except OSError:
        return None


def _invalidate_stale_artifact_chain(state: DistillState) -> bool:
    """Invalidate downstream artifacts when an upstream artifact is newer."""
    raw_m = _artifact_mtime(state, "raw_research.json")
    section_m = _artifact_mtime(state, "section_matches.json")
    generated_m = _artifact_mtime(state, "generated_payload.json")
    writebacks_m = _artifact_mtime(state, "writebacks.json")
    changed = False

    if raw_m is not None and section_m is not None and raw_m > section_m:
        logger.warning("raw_research.json is newer than section_matches.json")
        _invalidate_after_stage_r(state)
        changed = True
        section_m = None
        generated_m = None
        writebacks_m = None

    if section_m is not None and generated_m is not None and section_m > generated_m:
        logger.warning("section_matches.json is newer than generated_payload.json")
        _invalidate_after_stage_s(state)
        changed = True
        generated_m = None
        writebacks_m = None

    if generated_m is not None and writebacks_m is not None and generated_m > writebacks_m:
        logger.warning("generated_payload.json is newer than writebacks.json")
        _invalidate_after_stage_g(state)
        changed = True

    return changed


def _pipeline_done_contract(state: DistillState) -> tuple[bool, str]:
    """Check the durable contract required before a pipeline may be DONE."""
    if state.current_stage == "E":
        return False, "pending registry export"
    if not _artifact_exists(state, "raw_research.json"):
        return False, "missing raw_research.json"
    if not _artifact_exists(state, "section_matches.json"):
        return False, "missing section_matches.json"
    if not _artifact_exists(state, "generated_payload.json"):
        return False, "missing generated_payload.json"
    if not _artifact_exists(state, "registry_entry.json"):
        return False, "missing registry_entry.json"
    families = _theorem_family_names(state)
    if families and not _all_families_completed(state):
        missing = [name for name in families if name not in set(state.completed_families)]
        return False, "incomplete theorem families: " + ", ".join(missing)
    return True, "complete"


def _resume_stage_from_artifacts(state: DistillState) -> str:
    """Choose a conservative resume stage from local artifacts."""
    if not _artifact_exists(state, "raw_research.json"):
        return "R"
    if not _artifact_exists(state, "section_matches.json"):
        return "S"
    if not _artifact_exists(state, "generated_payload.json"):
        return "G"
    done, _reason = _pipeline_done_contract(state)
    if done:
        return "DONE"
    # If research and routing exist but completion is not proven, resume the
    # generative writeback/deepening stage.  Stage E is only a registry/export
    # transition and must not be inferred from old git commits.
    return "W"


def reconcile_state_contract(state: DistillState) -> DistillState:
    """Repair impossible stage states using local artifacts as source of truth."""
    artifacts_changed = _invalidate_stale_artifact_chain(state)
    family_markers_changed = _prune_completed_families(state)
    if state.current_stage not in STAGE_ORDER:
        old_stage = state.current_stage
        state.current_stage = _resume_stage_from_artifacts(state)
        save_state(state)
        logger.warning("State stage %s invalid; resumed at %s", old_stage, state.current_stage)
        return state

    if state.current_stage == "DONE":
        done, reason = _pipeline_done_contract(state)
        if not done:
            old_stage = state.current_stage
            state.current_stage = _resume_stage_from_artifacts(state)
            save_state(state)
            logger.warning(
                "State claimed DONE but contract failed (%s); resumed at %s",
                reason,
                state.current_stage,
            )
            logger.info("State contract repair: %s -> %s", old_stage, state.current_stage)
        elif artifacts_changed or family_markers_changed:
            save_state(state)
        return state

    required_before = {
        "S": "raw_research.json",
        "G": "section_matches.json",
        "W": "generated_payload.json",
        "E": "writebacks.json",
    }
    required = required_before.get(state.current_stage)
    if required and not _artifact_exists(state, required):
        old_stage = state.current_stage
        state.current_stage = _resume_stage_from_artifacts(state)
        save_state(state)
        logger.warning(
            "State stage %s lacked prerequisite %s; resumed at %s",
            old_stage,
            required,
            state.current_stage,
        )
    elif artifacts_changed or family_markers_changed:
        save_state(state)
    return state


def _raw_theorem_families(raw: Any) -> list[dict[str, Any]]:
    """Return well-formed theorem-family dictionaries from Stage R output."""
    if not isinstance(raw, dict):
        return []
    families = []
    for item in raw.get("theorem_families", []):
        if isinstance(item, dict):
            families.append(item)
    return families


def _payload_theorem_families(payload: Any) -> list[dict[str, Any]]:
    """Return theorem-family dictionaries from Stage G's scoped payload."""
    if not isinstance(payload, dict):
        return []
    knowledge = payload.get("knowledge_payload", {})
    if not isinstance(knowledge, dict):
        return []
    families = []
    for item in knowledge.get("theorem_families", []) or []:
        if isinstance(item, dict):
            families.append(item)
    return families


def _family_target_sections(raw: Any) -> list[str]:
    """Collect section slugs declared by the Stage R theorem inventory."""
    sections = []
    for family in _raw_theorem_families(raw):
        for section in _unique_strings(family.get("target_sections", [])):
            if section not in sections:
                sections.append(section)
    return sections


def _match_sections(matches: Any) -> list[str]:
    """Collect section slugs accepted by Stage S/S+."""
    if not isinstance(matches, dict):
        return []
    sections = []
    for item in matches.get("matches", []):
        if not isinstance(item, dict):
            continue
        section = str(item.get("section", "")).strip()
        if section and section not in sections:
            sections.append(section)
    return sections


def _coerce_sections(value: Any) -> list[str]:
    """Collect section-like strings from prompt payload fields."""
    sections = []
    if not isinstance(value, list):
        return sections
    for item in value:
        if isinstance(item, str):
            candidates = [item]
        elif isinstance(item, dict):
            candidates = [
                item.get("section"),
                item.get("name"),
                item.get("target"),
                item.get("tex_file"),
            ]
        else:
            candidates = [str(item)]
        for candidate in candidates:
            if not candidate:
                continue
            text = str(candidate).strip()
            section = text.split("/")[0] if text else ""
            if section and section not in sections:
                sections.append(section)
    return sections


def _payload_declared_sections(payload: Any) -> list[str]:
    """Collect target sections declared by Stage G output."""
    if not isinstance(payload, dict):
        return []
    sections = []
    for field_name in ("primary_targets",):
        for section in _coerce_sections(payload.get(field_name, [])):
            if section not in sections:
                sections.append(section)
    navigation = payload.get("navigation_payload", {})
    if isinstance(navigation, dict):
        for section in _coerce_sections(navigation.get("target_sections", [])):
            if section not in sections:
                sections.append(section)
    for field_name in ("frontier_chains", "coverage_debts", "expansion_queue"):
        for item in payload.get(field_name, []) or []:
            if not isinstance(item, dict):
                continue
            for key in ("target_sections", "sections", "section"):
                value = item.get(key)
                if isinstance(value, str):
                    value = [value]
                for section in _coerce_sections(value):
                    if section not in sections:
                        sections.append(section)
    return sections


def _scope_contract_from_artifacts(
    state: DistillState,
    raw: Any,
    matches: Any,
    payload: Any,
) -> dict[str, Any]:
    """Build the local scope contract that drives policy decisions."""
    family_names = [
        str(family.get("name", "")).strip()
        for family in _raw_theorem_families(raw)
        if str(family.get("name", "")).strip()
    ]
    method_names = []
    if isinstance(raw, dict):
        for item in raw.get("method_operators", []):
            if isinstance(item, dict):
                name = str(item.get("name", "")).strip()
                if name and name not in method_names:
                    method_names.append(name)
    mechanism_names = []
    if isinstance(raw, dict):
        for item in raw.get("bad_example_mechanisms", []):
            if isinstance(item, dict):
                name = str(item.get("name", "")).strip()
                if name and name not in mechanism_names:
                    mechanism_names.append(name)
    in_scope_sections = _family_target_sections(raw)
    target_sections = []
    for source in (
        in_scope_sections,
        _match_sections(matches),
        _payload_declared_sections(payload),
    ):
        for section in source:
            if section not in target_sections:
                target_sections.append(section)
    return {
        "version": POLICY_VERSION,
        "source": state.name,
        "source_slug": _slugify(state.name),
        "status": "active" if isinstance(raw, dict) else "seed",
        "objective": (
            "Distill source-specific mathematical operators into Omega only "
            "when they produce new, proof-closed, project-bound theorem chains."
        ),
        "theorem_families": family_names,
        "method_operators": method_names,
        "bad_example_mechanisms": mechanism_names,
        "target_sections": target_sections,
        "in_scope_target_sections": in_scope_sections,
        "hard_gates": [
            "scope_contract",
            "theorem_inventory",
            "semantic_scan_relevance",
            "payload_schema",
            "writeback_review",
            "family_closure",
            "done_contract",
        ],
        "split_policy": (
            "Strong material outside the declared theorem inventory is recorded "
            "as a split candidate and must not justify passing the current source."
        ),
        "distillation_memory": _distillation_memory_context(
            state,
            target_sections=target_sections,
        ),
    }


def _scope_contract_issues(raw: Any) -> list[str]:
    """Return hard issues in the Stage R scope contract."""
    if raw is None:
        return []
    if not isinstance(raw, dict):
        return ["raw_research.json is not a JSON object"]
    issues = []
    required = (
        "method_operators",
        "omega_object_mappings",
        "theorem_families",
        "bad_example_mechanisms",
        "frontier_interfaces",
        "novelty_guardrails",
    )
    for field_name in required:
        if not isinstance(raw.get(field_name), list) or not raw.get(field_name):
            issues.append(f"Stage R missing nonempty {field_name}")
    for idx, family in enumerate(_raw_theorem_families(raw), start=1):
        if not str(family.get("name", "")).strip():
            issues.append(f"theorem family {idx} has no name")
        if not _unique_strings(family.get("key_results", [])):
            issues.append(f"theorem family {idx} has no key_results")
        if not _unique_strings(family.get("target_sections", [])):
            issues.append(f"theorem family {idx} has no target_sections")
    return issues


def _derive_split_candidates(raw: Any, payload: Any, matches: Any) -> list[dict[str, Any]]:
    """Detect payload targets that should be externalized from this source."""
    if not isinstance(payload, dict):
        return []
    inventory_sections = set(_family_target_sections(raw))
    if not inventory_sections:
        return []
    matched_sections = set(_match_sections(matches))
    candidates = []
    for section in _payload_declared_sections(payload):
        if section in inventory_sections:
            continue
        evidence = "payload 目标不在 Stage R 的定理清单内"
        if section in matched_sections:
            evidence += "，但曾在语义路由中出现"
        candidates.append(
            {
                "section": section,
                "reason": evidence,
                "disposition": "record_for_split_or_future_source",
            }
        )
    return candidates


def _read_distillation_memory() -> dict[str, Any]:
    """Read the curated cross-run distillation memory ledger."""
    if not DISTILLATION_MEMORY_PATH.exists():
        return {"version": 1, "entries": []}
    data = read_json(DISTILLATION_MEMORY_PATH)
    if isinstance(data, list):
        return {"version": 1, "entries": data}
    if isinstance(data, dict):
        entries = data.get("entries", [])
        if not isinstance(entries, list):
            entries = []
        return {"version": int(data.get("version", 1) or 1), "entries": entries}
    return {"version": 1, "entries": []}


def _memory_entry_id(source_slug: str, kind: str, title: str, reason: str) -> str:
    digest = hashlib.sha1(f"{source_slug}|{kind}|{title}|{reason}".encode("utf-8")).hexdigest()
    return f"{source_slug}:{kind}:{digest[:12]}"


def _compact_scope_context(scope: dict[str, Any]) -> dict[str, Any]:
    """Keep only compact scope metadata that is useful across runs."""
    return {
        "family_count": len(_unique_strings(scope.get("theorem_families", []))),
        "in_scope_target_sections": _unique_strings(
            scope.get("in_scope_target_sections", scope.get("target_sections", []))
        ),
    }


def _upsert_distillation_memory(entries: list[dict[str, Any]]) -> dict[str, Any]:
    """Upsert compact, curated memory entries that are safe to commit."""
    if not entries:
        return _read_distillation_memory()
    memory = _read_distillation_memory()
    existing = {
        str(entry.get("id", "")): entry
        for entry in memory.get("entries", [])
        if isinstance(entry, dict) and entry.get("id")
    }
    now = _now_iso()
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        entry_id = str(entry.get("id", "")).strip()
        if not entry_id:
            continue
        previous = existing.get(entry_id, {})
        merged = {**previous, **entry}
        merged.setdefault("created_at", previous.get("created_at") or now)
        previous_compare = {k: v for k, v in previous.items() if k != "updated_at"}
        merged_compare = {k: v for k, v in merged.items() if k != "updated_at"}
        if previous and previous_compare == merged_compare:
            merged["updated_at"] = previous.get("updated_at", now)
        else:
            merged["updated_at"] = now
        existing[entry_id] = merged
    output = {
        "version": 1,
        "description": "蒸馏记忆账本，仅保留可复用的拆分候选与旁路结论；原始中间产物留在 .distillation 且不提交。",
        "entries": sorted(existing.values(), key=lambda item: str(item.get("id", ""))),
    }
    write_json(DISTILLATION_MEMORY_PATH, output)
    return output


def _memory_entries_from_split_candidates(state: DistillState) -> list[dict[str, Any]]:
    """Convert policy split candidates into durable future-context entries."""
    source_slug = _slugify(state.name)
    scope = state.scope_contract or {}
    entries = []
    for candidate in state.split_candidates:
        if not isinstance(candidate, dict):
            continue
        section = str(candidate.get("section", "")).strip()
        reason = str(candidate.get("reason", "")).strip()
        if not section or not reason:
            continue
        title = f"{state.name}：待拆分候选（{section}）"
        entries.append(
            {
                "id": _memory_entry_id(source_slug, "split_candidate", section, reason),
                "kind": "split_candidate",
                "status": "open",
                "source": state.name,
                "source_slug": source_slug,
                "title": title,
                "target_sections": [section],
                "scope_relation": "outside_current_source_scope",
                "origin": "policy.split_candidate",
                "reason": reason,
                "disposition": candidate.get("disposition", "record_for_split_or_future_source"),
                "current_scope": _compact_scope_context(scope),
                "reuse_guidance": "仅在后续 scope contract 明确吸收该项时再加载；不得用它直接帮助当前来源过门禁。",
            }
        )
    return entries


def _memory_entries_from_oracle_sidecar(
    state: DistillState,
    data: dict[str, Any],
    focused_family: Optional[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Convert Oracle sidecar candidates into durable future-context entries."""
    source_slug = _slugify(state.name)
    family_name = str((focused_family or {}).get("name", "")).strip()
    entries = []
    for item in data.get("sidecar_candidates", []) or []:
        if not isinstance(item, dict):
            continue
        title = str(item.get("title", "")).strip()
        reason = str(item.get("source_reason", item.get("reason", ""))).strip()
        if not title or not reason:
            continue
        target_sections = _unique_strings(item.get("target_sections", []))
        entries.append(
            {
                "id": _memory_entry_id(source_slug, "oracle_sidecar", title, reason),
                "kind": "oracle_sidecar",
                "status": str(item.get("status", "open") or "open"),
                "source": state.name,
                "source_slug": source_slug,
                "title": title,
                "target_sections": target_sections,
                "scope_relation": str(item.get("scope_relation", "side_result") or "side_result"),
                "origin": "oracle.deepening",
                "focused_family": family_name,
                "reason": reason,
                "reuse_guidance": str(
                    item.get(
                        "reuse_guidance",
                        "仅在后续 scope contract 明确吸收该旁路结论时再加载。",
                    )
                ),
            }
        )
    return entries


def _distillation_memory_context(
    state: DistillState,
    target_sections: Optional[list[str]] = None,
    limit: int = 12,
) -> list[dict[str, Any]]:
    """Return compact memory entries relevant to the current source or targets."""
    memory = _read_distillation_memory()
    source_slug = _slugify(state.name)
    target_set = set(target_sections or [])
    relevant = []
    for entry in memory.get("entries", []):
        if not isinstance(entry, dict):
            continue
        sections = set(_unique_strings(entry.get("target_sections", [])))
        same_source = entry.get("source_slug") == source_slug
        overlaps = bool(target_set and sections & target_set)
        if same_source or overlaps:
            relevant.append(
                {
                    "id": entry.get("id"),
                    "kind": entry.get("kind"),
                    "status": entry.get("status"),
                    "title": entry.get("title"),
                    "target_sections": list(sections),
                    "scope_relation": entry.get("scope_relation"),
                    "reason": entry.get("reason"),
                    "reuse_guidance": entry.get("reuse_guidance"),
                }
            )
    return relevant[-limit:]


def _active_coverage_debts(payload: Any, completed_families: list[str]) -> list[dict[str, Any]]:
    """Return unresolved coverage debts from Stage G output."""
    if not isinstance(payload, dict):
        return []
    completed = set(completed_families)
    active = []
    for item in payload.get("coverage_debts", []) or []:
        if not isinstance(item, dict):
            continue
        family = str(item.get("family", "")).strip()
        if family and family in completed:
            continue
        active.append(item)
    return active


def _writeback_status(writebacks: Any) -> str:
    """Return the current writeback artifact status."""
    if not isinstance(writebacks, dict):
        return ""
    return str(writebacks.get("status", "")).strip()


def _review_score_summary(state: DistillState) -> dict[str, Any]:
    """Summarize persisted review scores for policy status."""
    minimums = []
    latest_key = ""
    latest_passed: Optional[bool] = None
    for key, value in state.scores.items():
        if not isinstance(value, dict):
            continue
        latest_key = key
        if "gate_passed" in value:
            latest_passed = bool(value.get("gate_passed"))
        minimum = value.get("minimum_score")
        if minimum is None:
            numeric = [
                float(score)
                for score in (
                    value.get("codex", {}).get("score"),
                    value.get("claude", {}).get("score"),
                    value.get("oracle", {}).get("score"),
                )
                if isinstance(score, (int, float))
            ]
            minimum = min(numeric) if numeric else None
        if isinstance(minimum, (int, float)):
            minimums.append(float(minimum))
    return {
        "latest": latest_key,
        "minimum_seen": min(minimums) if minimums else None,
        "latest_passed": (
            latest_passed
            if latest_passed is not None
            else bool(minimums and minimums[-1] >= SCORE_PASS_THRESHOLD)
        ),
    }


def _build_inventory_snapshot(
    state: DistillState,
    raw: Any,
    matches: Any,
    payload: Any,
    writebacks: Any,
    registry_entry: Any,
    blocked_artifact: Any,
) -> dict[str, Any]:
    """Build the theorem inventory and gate snapshot for the policy loop."""
    family_names = [
        str(family.get("name", "")).strip()
        for family in _raw_theorem_families(raw)
        if str(family.get("name", "")).strip()
    ]
    completed = [
        name for name in state.completed_families
        if name in family_names or not family_names
    ]
    missing = [name for name in family_names if name not in set(completed)]
    match_rows = matches.get("matches", []) if isinstance(matches, dict) else []
    semantic_rows = [
        item for item in match_rows
        if isinstance(item, dict) and str(item.get("match_source", "")).startswith("semantic")
    ]
    payload_errors = (
        _validate_generated_payload(payload)
        if isinstance(payload, dict)
        else []
    )
    done, done_reason = _pipeline_done_contract(state)
    split_candidates = _derive_split_candidates(raw, payload, matches)
    active_debts = _active_coverage_debts(payload, state.completed_families)
    return {
        "artifacts": {
            "raw_research": isinstance(raw, dict),
            "section_matches": isinstance(matches, dict),
            "global_evidence_pack": _artifact_exists(state, "global_evidence_pack.json"),
            "generated_payload": isinstance(payload, dict),
            "writebacks": isinstance(writebacks, dict),
            "registry_entry": isinstance(registry_entry, dict),
            "blocked": isinstance(blocked_artifact, dict),
        },
        "scope_issues": _scope_contract_issues(raw),
        "families": family_names,
        "completed_families": completed,
        "missing_families": missing,
        "match_count": len(match_rows),
        "semantic_match_count": len(semantic_rows),
        "payload_errors": payload_errors,
        "writeback_status": _writeback_status(writebacks),
        "active_coverage_debts": active_debts,
        "split_candidates": split_candidates,
        "blocked_artifact": blocked_artifact if isinstance(blocked_artifact, dict) else {},
        "review_scores": _review_score_summary(state),
        "done_contract": {"passed": done, "reason": done_reason},
    }


def _open_debts_from_inventory(inventory: dict[str, Any]) -> list[dict[str, Any]]:
    """Translate inventory misses into policy debts."""
    debts = []
    for family in inventory.get("missing_families", []):
        debts.append({"type": "theorem_family", "family": family})
    for debt in inventory.get("active_coverage_debts", []):
        debts.append({"type": "coverage_debt", **debt})
    for issue in inventory.get("payload_errors", []):
        debts.append({"type": "payload_schema", "reason": issue})
    if inventory.get("artifacts", {}).get("section_matches") and inventory.get("match_count") == 0:
        debts.append({"type": "empty_scan", "reason": "Stage S produced no relevant targets"})
    blocked = inventory.get("blocked_artifact", {})
    if blocked:
        debts.append(
            {
                "type": "blocked_stage",
                "stage": blocked.get("stage"),
                "status": blocked.get("status"),
                "depth_cycle": blocked.get("depth_cycle"),
            }
        )
    return debts


def _plan_next_action(
    state: DistillState,
    inventory: dict[str, Any],
) -> dict[str, Any]:
    """Choose the next pipeline action from hard gates, not round count."""
    artifacts = inventory.get("artifacts", {})
    done_contract = inventory.get("done_contract", {})
    if done_contract.get("passed"):
        return {
            "action": "done",
            "stage": "DONE",
            "gate": "done_contract",
            "reason": "all durable completion requirements are satisfied",
        }
    if not artifacts.get("raw_research"):
        return {
            "action": "run_stage",
            "stage": "R",
            "gate": "scope_contract",
            "reason": "build source scope contract and theorem inventory",
        }
    if inventory.get("scope_issues"):
        return {
            "action": "run_stage",
            "stage": "R",
            "gate": "scope_contract",
            "reason": "; ".join(inventory["scope_issues"][:3]),
        }
    if not artifacts.get("section_matches") or not artifacts.get("global_evidence_pack"):
        return {
            "action": "run_stage",
            "stage": "S",
            "gate": "semantic_scan_relevance",
            "reason": "build relevant section routing and whole-article evidence pack",
        }
    if inventory.get("match_count", 0) == 0:
        return {
            "action": "blocked",
            "stage": state.current_stage,
            "gate": "semantic_scan_relevance",
            "reason": "Stage S produced no relevant section matches",
        }
    if not artifacts.get("generated_payload"):
        return {
            "action": "run_stage",
            "stage": "G",
            "gate": "payload_schema",
            "reason": "generate theorem-chain payload from scoped evidence",
        }
    if inventory.get("payload_errors"):
        return {
            "action": "run_stage",
            "stage": "G",
            "gate": "payload_schema",
            "reason": "; ".join(inventory["payload_errors"][:3]),
        }
    writeback_status = inventory.get("writeback_status", "")
    if writeback_status in {"rejected", "skipped"}:
        return {
            "action": "run_stage",
            "stage": "W",
            "gate": "writeback_review",
            "reason": f"writeback artifact status is {writeback_status}",
        }
    if not artifacts.get("writebacks"):
        return {
            "action": "run_stage",
            "stage": "W",
            "gate": "writeback_review",
            "reason": "produce reviewed theorem writebacks",
        }
    if state.current_stage == "E":
        return {
            "action": "run_stage",
            "stage": "E",
            "gate": "registry_export",
            "reason": "export the current accepted writeback cycle before further deepening",
        }
    if not artifacts.get("registry_entry"):
        return {
            "action": "run_stage",
            "stage": "E",
            "gate": "registry_export",
            "reason": "export accepted writebacks and advance family deepening",
        }
    if inventory.get("missing_families"):
        return {
            "action": "run_stage",
            "stage": "W",
            "gate": "family_closure",
            "reason": "incomplete theorem families: "
            + ", ".join(inventory["missing_families"][:5]),
        }
    return {
        "action": "blocked",
        "stage": state.current_stage,
        "gate": "done_contract",
        "reason": str(done_contract.get("reason", "unclassified completion failure")),
    }


def _policy_model(state: DistillState) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Build scope, inventory, and next action without writing artifacts."""
    raw = _read_artifact_json_or_none(state, "raw_research.json")
    matches = _read_artifact_json_or_none(state, "section_matches.json")
    payload = _read_artifact_json_or_none(state, "generated_payload.json")
    writebacks = _read_artifact_json_or_none(state, "writebacks.json")
    registry_entry = _read_artifact_json_or_none(state, "registry_entry.json")
    blocked_artifact = _read_artifact_json_or_none(state, "blocked.json")
    scope = _scope_contract_from_artifacts(state, raw, matches, payload)
    inventory = _build_inventory_snapshot(
        state,
        raw,
        matches,
        payload,
        writebacks,
        registry_entry,
        blocked_artifact,
    )
    action = _plan_next_action(state, inventory)
    return scope, inventory, action


def refresh_policy_state(state: DistillState, *, persist: bool = True) -> dict[str, Any]:
    """Persist the local policy snapshot and return the next action."""
    scope, inventory, action = _policy_model(state)
    state.scope_contract = scope
    state.open_debts = _open_debts_from_inventory(inventory)
    state.split_candidates = inventory.get("split_candidates", [])
    if persist:
        _upsert_distillation_memory(_memory_entries_from_split_candidates(state))
    state.blocked = (
        {
            "active": True,
            "gate": action.get("gate"),
            "stage": action.get("stage"),
            "reason": action.get("reason"),
            "updated_at": _now_iso(),
        }
        if action.get("action") == "blocked"
        else inventory.get("blocked_artifact", {})
    )
    state.policy_state = {
        "version": POLICY_VERSION,
        "updated_at": _now_iso(),
        "current_stage": state.current_stage,
        "next_action": action,
        "inventory": {
            "artifacts": inventory.get("artifacts", {}),
            "families": len(inventory.get("families", [])),
            "completed_families": len(inventory.get("completed_families", [])),
            "missing_families": inventory.get("missing_families", []),
            "match_count": inventory.get("match_count", 0),
            "semantic_match_count": inventory.get("semantic_match_count", 0),
            "payload_error_count": len(inventory.get("payload_errors", [])),
            "open_debt_count": len(state.open_debts),
            "split_candidate_count": len(state.split_candidates),
            "done_contract": inventory.get("done_contract", {}),
        },
    }
    if persist:
        save_state(state)
    return action


def rebuild_from_git(name: str) -> DistillState:
    """Recover pipeline state from git commit history after crash/reset.

    Local state/artifacts are authoritative.  Git history is only a weak
    fallback for a missing state directory; it must never advance an incomplete
    deepening cycle to DONE.
    """
    state = load_state(name)
    state_path = _artifact_path(state, "state.json")
    if state_path.exists():
        return reconcile_state_contract(state)

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

    max_stage_idx = STAGE_ORDER.index(_resume_stage_from_artifacts(state))
    max_round = state.round_number
    for line in result.stdout.splitlines():
        m = re.search(
            rf"distill\({re.escape(slug)}\):\s*stage\s+(\w)\s+\((\w+)\)\s+complete",
            line,
        )
        if m:
            stage_letter = m.group(1)
            if stage_letter in STAGE_ORDER[:-1]:
                idx = STAGE_ORDER.index(stage_letter)
                # Advance to the stage AFTER the completed one
                next_idx = min(idx + 1, STAGE_ORDER.index("E"))
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
    return reconcile_state_contract(state)


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
        "bad_example_mechanisms": [
            {
                "name": "dry_run_minimal_obstruction_skeleton",
                "worst_counterexample_shape": "a minimal object failing one audited compatibility layer",
                "classification_skeletons": ["sticky", "holonomy", "budget"],
                "closure_route": "show that the skeleton either descends or violates a finite budget bound",
            }
        ],
        "frontier_interfaces": [
            {
                "omega_interface": "folding/pom/logic_expansion_chain",
                "source_tool": "dry-run structural transport",
                "publishable_question": "whether minimal bad objects admit a canonical skeleton decomposition",
                "risk": "dry-run placeholder rather than source-backed mathematics",
            }
        ],
        "novelty_guardrails": [
            "Do not restate finite descent without an Omega-specific obstruction."
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


def run_stage_r(
    state: DistillState,
    dry_run: bool = False,
    oracle_research: bool = False,
    oracle_timeout: int = DEFAULT_ORACLE_TIMEOUT,
    oracle_model: str = DEFAULT_ORACLE_MODEL,
    oracle_pdf: Optional[Path] = None,
) -> bool:
    """Run Stage R research extraction and persist raw research JSON."""
    logger.info("Stage R starting for %s", state.name)
    required = [
        "mathematician",
        "method_operators",
        "omega_object_mappings",
        "theorem_families",
        "bad_example_mechanisms",
        "frontier_interfaces",
        "novelty_guardrails",
        "search_directives",
        "induction_templates",
        "failure_modes",
        "router_triggers",
    ]
    feedback = ""
    for attempt in range(1, 4):
        if dry_run:
            data = _dry_raw_research(state.name)
        elif oracle_research and attempt == 1:
            prompt = _load_prompt("oracle_research").format(
                mathematician=state.name,
                current_datetime=datetime.now().astimezone().isoformat(timespec="seconds"),
                section_list=_section_list(),
                euclid_example=_euclid_example(),
                deep_research_directive=_deep_research_directive(),
                schema=_research_schema(),
            )
            response = chatgpt_oracle_exec(
                state,
                prompt,
                log_tag="R_oracle",
                timeout_seconds=oracle_timeout,
                model=oracle_model,
                pdf_path=oracle_pdf,
                dry_run=False,
            )
            if not response:
                feedback = "ChatGPT Oracle produced no response; falling back to Codex Stage R"
                state.prior_feedback.append(f"R oracle attempt: {feedback}")
                logger.warning(feedback)
                continue
            try:
                data = _extract_json(response)
                if isinstance(data, dict):
                    data.setdefault(
                        "oracle_research_metadata",
                        {
                            "source": "chatgpt_oracle",
                            "model": oracle_model,
                            "timestamp": _now_iso(),
                        },
                    )
            except (ValueError, json.JSONDecodeError) as exc:
                feedback = f"Could not parse Oracle JSON: {exc}"
                state.prior_feedback.append(f"R oracle attempt: {feedback}")
                logger.warning(feedback)
                continue
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
            response = _codex_exec_with_infra_retries(
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
            _invalidate_after_stage_r(state)
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
                "match": score >= PYTHON_SCAN_MATCH_THRESHOLD,
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


def _scan_tex_path(rel: str) -> Optional[Path]:
    """Resolve a scan target safely under CORE_BODY."""
    if not rel:
        return None
    path = (CORE_BODY / rel).resolve()
    try:
        path.relative_to(CORE_BODY.resolve())
    except ValueError:
        return None
    if path.suffix != ".tex":
        return None
    return path


def _scan_candidate_contexts(section_scores: list[dict[str, Any]]) -> str:
    """Format compact contexts for Stage S+ semantic reranking."""
    chunks = []
    for item in section_scores[:SEMANTIC_SCAN_CANDIDATES]:
        rel = str(item.get("tex_file", ""))
        path = _scan_tex_path(rel)
        if not path or not path.exists():
            continue
        text = read_text(path)
        if len(text) > SEMANTIC_SCAN_CONTEXT_CHARS:
            text = text[:SEMANTIC_SCAN_CONTEXT_CHARS] + "\n% [context truncated by semantic scan]\n"
        compact = {
            "section": item.get("section"),
            "tex_file": rel,
            "python_score": item.get("score"),
            "coverage": item.get("coverage"),
            "counts": item.get("counts"),
            "unique_triggers": item.get("unique_triggers", [])[:10],
        }
        chunks.append(f"--- candidate ---\n{_json_block(compact)}\n{text}")
    return "\n\n".join(chunks)


def _compact_ws(text: str, limit: int = GLOBAL_EVIDENCE_SNIPPET_CHARS) -> str:
    """Collapse whitespace and trim a snippet for global evidence packs."""
    compact = re.sub(r"\s+", " ", text).strip()
    if len(compact) > limit:
        return compact[:limit].rstrip() + " ..."
    return compact


def _evidence_terms(raw_research: dict[str, Any]) -> list[str]:
    """Build high-signal whole-article search terms from research and strategy."""
    terms = _normalize_triggers(raw_research.get("router_triggers", []))
    for field_name in ("search_directives", "induction_templates", "failure_modes"):
        for item in raw_research.get(field_name, []) or []:
            if isinstance(item, str):
                terms.extend(re.findall(r"[A-Za-z][A-Za-z0-9_-]{3,}|[\u4e00-\u9fff]{2,}", item))
    fixed_terms = [
        "fold-aware",
        "inverse system",
        "stable inverse",
        "pseudo-invariant",
        "near-extremal",
        "maximal fiber",
        "sticky",
        "Frostman",
        "slab",
        "sector",
        "escort",
        "freezing",
        "moment",
        "Cech",
        "\\v{C}ech",
        "holonomy",
        "curvature",
        "Walsh",
        "Stokes",
        "Euler",
        "capacity",
        "prime-register",
        "external ledger",
        "budget",
        "gluing",
        "obstruction",
        "counterexample",
        "localization",
        "normalization",
        "externalization",
        "坏例子",
        "反例",
        "骨架",
        "粘接",
        "障碍",
        "预算",
        "外置",
        "冻结",
        "纤维",
        "曲率",
    ]
    terms.extend(fixed_terms)
    seen = set()
    result = []
    for term in terms:
        value = str(term).strip()
        key = value.lower()
        if len(value) < 2 or key in seen:
            continue
        seen.add(key)
        result.append(value)
    return result[:90]


def _term_hit_score(text: str, terms: list[str]) -> tuple[int, list[str]]:
    """Return a simple evidence relevance score and matched terms."""
    matched = []
    score = 0
    for term in terms:
        if re.search(re.escape(term), text, re.IGNORECASE):
            matched.append(term)
            score += 1
    return score, matched


def _interface_snippets(text: str, terms: list[str]) -> list[dict[str, Any]]:
    """Extract compact snippets around unfinished or frontier-like terms."""
    interface_terms = [
        "TODO",
        "FIXME",
        "conjecture",
        "Conjecture",
        "open",
        "interface",
        "oracle",
        "capacity",
        "budget",
        "obstruction",
        "holonomy",
        "Cech",
        "\\v{C}ech",
        "fold",
        "Fold",
        "external",
        "ledger",
        "sticky",
        "Frostman",
        "slab",
        "未完成",
        "接口",
        "猜想",
        "障碍",
        "预算",
        "外置",
        "闭包",
    ]
    snippets = []
    for term in interface_terms:
        match = re.search(re.escape(term), text, re.IGNORECASE)
        if not match:
            continue
        start = max(0, match.start() - 350)
        end = min(len(text), match.end() + 550)
        snippet = text[start:end]
        score, matched = _term_hit_score(snippet, terms)
        snippets.append(
            {
                "term": term,
                "score": score,
                "matched_terms": matched[:8],
                "snippet": _compact_ws(snippet),
            }
        )
        if len(snippets) >= 3:
            break
    return snippets


def _build_global_evidence_pack(
    raw_research: dict[str, Any],
    section_scores: list[dict[str, Any]],
) -> dict[str, Any]:
    """Summarize whole-article LaTeX evidence for semantic routing.

    This deliberately stays compact: it lets models see the whole article's
    section topology and high-signal claims without flooding the prompt with
    thousands of source files.
    """
    terms = _evidence_terms(raw_research)
    section_index = [
        {
            "section": item.get("section"),
            "best_file": item.get("tex_file"),
            "python_score": item.get("score"),
            "coverage": item.get("coverage"),
            "counts": item.get("counts"),
            "unique_triggers": item.get("unique_triggers", [])[:8],
            "file_count": item.get("file_count"),
        }
        for item in section_scores
    ]

    claim_rows: list[dict[str, Any]] = []
    distill_rows: list[dict[str, Any]] = []
    interface_rows: list[dict[str, Any]] = []
    if not CORE_BODY.exists():
        return {
            "terms": terms,
            "section_index": section_index,
            "high_signal_claims": [],
            "existing_distillation_claims": [],
            "frontier_interfaces": [],
        }

    for tex_file in sorted(path for path in CORE_BODY.rglob("*.tex") if path.is_file()):
        rel = tex_file.relative_to(CORE_BODY).as_posix()
        section = rel.split("/")[0]
        try:
            text = read_text(tex_file)
        except OSError:
            continue

        for claim in _extract_claims(text):
            claim_text = claim.get("text", "")
            score, matched = _term_hit_score(claim_text, terms)
            label = claim.get("label", "")
            row = {
                "section": section,
                "tex_file": rel,
                "type": claim.get("type"),
                "label": label,
                "score": score + (3 if "distill" in label else 0),
                "matched_terms": matched[:10],
                "snippet": _compact_ws(claim_text),
            }
            if "distill" in label:
                distill_rows.append(row)
            if score > 0:
                claim_rows.append(row)

        for snippet in _interface_snippets(text, terms):
            snippet["section"] = section
            snippet["tex_file"] = rel
            interface_rows.append(snippet)

    claim_rows.sort(key=lambda item: int(item.get("score", 0)), reverse=True)
    distill_rows.sort(key=lambda item: int(item.get("score", 0)), reverse=True)
    interface_rows.sort(key=lambda item: int(item.get("score", 0)), reverse=True)
    return {
        "terms": terms,
        "source_theorem_families": raw_research.get("theorem_families", []),
        "section_index": section_index,
        "high_signal_claims": claim_rows[:GLOBAL_EVIDENCE_MAX_CLAIMS],
        "existing_distillation_claims": distill_rows[:GLOBAL_EVIDENCE_MAX_CLAIMS],
        "frontier_interfaces": interface_rows[:GLOBAL_EVIDENCE_MAX_INTERFACES],
    }


def _global_evidence_for_state(state: DistillState) -> dict[str, Any]:
    """Read a persisted evidence pack, falling back to a compact rebuild."""
    path = _artifact_path(state, "global_evidence_pack.json")
    if path.exists():
        try:
            pack = read_json(path)
            if isinstance(pack, dict):
                pack["distillation_memory"] = _distillation_memory_context(
                    state,
                    target_sections=_payload_declared_sections(
                        _read_artifact_json_or_none(state, "generated_payload.json")
                    ),
                )
                return pack
        except (OSError, json.JSONDecodeError):
            pass
    try:
        raw = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError:
        return {}
    try:
        matches = _read_artifact_json(state, "section_matches.json")
        section_scores = matches.get("all_sections", [])
    except FileNotFoundError:
        section_scores = []
    pack = _build_global_evidence_pack(raw, section_scores)
    pack["distillation_memory"] = _distillation_memory_context(
        state,
        target_sections=_payload_declared_sections(
            _read_artifact_json_or_none(state, "generated_payload.json")
        ),
    )
    return pack


def _prompt_snippet(text: Any, max_chars: int) -> str:
    """Return a compact single-string prompt snippet."""
    value = str(text or "").strip()
    if len(value) <= max_chars:
        return value
    return value[:max_chars].rstrip() + "..."


def _oracle_compact_evidence_row(row: dict[str, Any]) -> dict[str, Any]:
    """Keep only target-routing fields needed by the browser Oracle prompt."""
    compact: dict[str, Any] = {}
    for key in ("section", "tex_file", "type", "label", "term", "score", "python_score"):
        value = row.get(key)
        if value not in (None, "", []):
            compact[key] = value
    matched_terms = _unique_strings(row.get("matched_terms", []))[:6]
    if matched_terms:
        compact["matched_terms"] = matched_terms
    snippet = _prompt_snippet(row.get("snippet", ""), ORACLE_EVIDENCE_SNIPPET_CHARS)
    if snippet:
        compact["snippet"] = snippet
    return compact


def _oracle_compact_section_index_row(row: dict[str, Any]) -> dict[str, Any]:
    """Keep section-index rows short enough for ChatGPT browser injection."""
    compact: dict[str, Any] = {}
    for key in ("section", "best_file", "python_score", "coverage"):
        value = row.get(key)
        if value not in (None, "", []):
            compact[key] = value
    triggers = _unique_strings(row.get("unique_triggers", []))[:6]
    if triggers:
        compact["unique_triggers"] = triggers
    return compact


def _oracle_relevant_evidence_pack(
    global_evidence_pack: dict[str, Any],
    focused_family: Optional[dict[str, Any]],
    targets: list[dict[str, Any]],
) -> dict[str, Any]:
    """Compress whole-article evidence into a target-focused Oracle summary."""
    if not isinstance(global_evidence_pack, dict):
        return {}
    target_sections = set(_unique_strings((focused_family or {}).get("target_sections", [])))
    target_sections.update(
        str(item.get("section", "")).strip()
        for item in targets
        if isinstance(item, dict) and str(item.get("section", "")).strip()
    )

    def _row_rank(row: Any) -> tuple[int, int, str]:
        if not isinstance(row, dict):
            return (0, 0, "")
        section = str(row.get("section", "")).strip()
        hit = 1 if section in target_sections else 0
        score = int(row.get("score", 0) or 0)
        return (hit, score, section)

    def _trim_rows(key: str, limit: int) -> list[dict[str, Any]]:
        rows = [row for row in global_evidence_pack.get(key, []) if isinstance(row, dict)]
        rows.sort(key=_row_rank, reverse=True)
        return [_oracle_compact_evidence_row(row) for row in rows[:limit]]

    section_index = [row for row in global_evidence_pack.get("section_index", []) if isinstance(row, dict)]
    section_index.sort(
        key=lambda row: (
            1 if str(row.get("section", "")).strip() in target_sections else 0,
            int(row.get("python_score", 0) or 0),
            str(row.get("section", "")).strip(),
        ),
        reverse=True,
    )

    theorem_families = []
    for item in global_evidence_pack.get("source_theorem_families", []) or []:
        if not isinstance(item, dict):
            continue
        theorem_families.append(
            {
                "name": str(item.get("name", "")).strip(),
                "target_sections": _unique_strings(item.get("target_sections", [])),
                "key_results": [
                    _prompt_snippet(result, 220)
                    for result in _unique_strings(item.get("key_results", []))[:3]
                ],
            }
        )

    memory_rows = [row for row in global_evidence_pack.get("distillation_memory", []) if isinstance(row, dict)]
    memory_rows.sort(
        key=lambda row: (
            1 if set(_unique_strings(row.get("target_sections", []))) & target_sections else 0,
            1 if row.get("kind") == "oracle_sidecar" else 0,
            str(row.get("id", "")),
        ),
        reverse=True,
    )

    return {
        "terms": _unique_strings(global_evidence_pack.get("terms", []))[:20],
        "focused_target_sections": sorted(target_sections),
        "source_theorem_families": theorem_families[:8],
        "section_index": [
            _oracle_compact_section_index_row(row)
            for row in section_index[:ORACLE_EVIDENCE_MAX_SECTION_INDEX]
        ],
        "high_signal_claims": _trim_rows("high_signal_claims", ORACLE_EVIDENCE_MAX_CLAIMS),
        "existing_distillation_claims": _trim_rows(
            "existing_distillation_claims",
            ORACLE_EVIDENCE_MAX_EXISTING,
        ),
        "frontier_interfaces": _trim_rows(
            "frontier_interfaces",
            ORACLE_EVIDENCE_MAX_INTERFACES,
        ),
        "distillation_memory": [
            {
                "id": str(row.get("id", "")).strip(),
                "kind": str(row.get("kind", "")).strip(),
                "status": str(row.get("status", "")).strip(),
                "title": _prompt_snippet(row.get("title", ""), 160),
                "target_sections": _unique_strings(row.get("target_sections", [])),
                "reason": _prompt_snippet(row.get("reason", ""), 240),
                "reuse_guidance": _prompt_snippet(row.get("reuse_guidance", ""), 240),
            }
            for row in memory_rows[:ORACLE_EVIDENCE_MAX_MEMORY]
        ],
    }


def _oracle_payload_summary(
    payload: dict[str, Any],
    focused_family: Optional[dict[str, Any]],
) -> dict[str, Any]:
    """Compress generated payload into the Oracle-relevant working contract."""
    if not isinstance(payload, dict):
        return {}
    family_name = str((focused_family or {}).get("name", "")).strip()
    family_targets = set(_unique_strings((focused_family or {}).get("target_sections", [])))

    coverage_debts = []
    for item in payload.get("coverage_debts", []) or []:
        if not isinstance(item, dict):
            continue
        debt_family = str(item.get("family", "")).strip()
        debt_targets = _unique_strings(item.get("target_sections", []))
        if family_name and debt_family and debt_family != family_name:
            if not (family_targets and set(debt_targets) & family_targets):
                continue
        coverage_debts.append(
            {
                "family": debt_family,
                "type": str(item.get("type", "")).strip(),
                "reason": str(item.get("reason", "")).strip(),
                "target_sections": debt_targets,
            }
        )
        if len(coverage_debts) >= 6:
            break

    frontier_chains = []
    for item in payload.get("frontier_chains", []) or []:
        if isinstance(item, dict):
            frontier_chains.append(
                {
                    "title": str(item.get("proposed_title", item.get("title", ""))).strip(),
                    "reason": str(
                        item.get("reason", item.get("novelty_reason", ""))
                    ).strip(),
                    "target_sections": _unique_strings(item.get("target_sections", [])),
                }
            )
        else:
            text = str(item).strip()
            if text:
                frontier_chains.append(text)
        if len(frontier_chains) >= 6:
            break

    expansion_queue = []
    for item in payload.get("expansion_queue", []) or []:
        if not isinstance(item, dict):
            continue
        target_sections = _unique_strings(item.get("target_sections", []))
        if family_targets and target_sections and not (set(target_sections) & family_targets):
            continue
        expansion_queue.append(
            {
                "status": str(item.get("status", "active") or "active"),
                "target_sections": target_sections,
                "kernel": str(item.get("kernel", "")).strip(),
            }
        )
        if len(expansion_queue) >= 6:
            break

    return {
        "source_slug": payload.get("knowledge_payload", {}).get("source_slug"),
        "source_type": payload.get("knowledge_payload", {}).get("source_type"),
        "primary_targets": _unique_strings(payload.get("primary_targets", [])),
        "navigation_targets": _unique_strings(
            payload.get("navigation_payload", {}).get("target_sections", [])
        ),
        "closure_criteria": _unique_strings(payload.get("closure_criteria", []))[:8],
        "frontier_chains": frontier_chains,
        "coverage_debts": coverage_debts,
        "expansion_queue": expansion_queue,
    }


def _semantic_scan(
    state: DistillState,
    raw_research: dict[str, Any],
    section_scores: list[dict[str, Any]],
    global_evidence_pack: dict[str, Any],
    dry_run: bool,
) -> dict[str, Any]:
    """Run the model-assisted Stage S+ scan over deterministic candidates."""
    if dry_run:
        return {
            "status": "dry_run",
            "semantic_matches": [],
            "frontier_chains": [],
            "rejects": [],
        }
    candidates = section_scores[:SEMANTIC_SCAN_CANDIDATES]
    prompt = _load_prompt("semantic_scan").format(
        mathematician=state.name,
        raw_research=_json_block(raw_research),
        deterministic_scores=_json_block(candidates),
        global_evidence_pack=_json_block(global_evidence_pack),
        candidate_contexts=_scan_candidate_contexts(section_scores),
        deep_research_directive=_deep_research_directive(),
        schema=_semantic_scan_schema(),
    )
    response = _codex_exec_with_infra_retries(
        prompt,
        work_dir=REPO_ROOT,
        timeout_seconds=1200,
        dry_run=False,
        log_tag=f"{_slugify(state.name)}_S_semantic",
    )
    try:
        data = _extract_json(response)
    except (ValueError, json.JSONDecodeError) as exc:
        logger.warning("Stage S+ semantic scan failed to parse JSON: %s", exc)
        return {
            "status": "parse_failed",
            "semantic_matches": [],
            "frontier_chains": [],
            "rejects": [],
            "raw_response": response[:4000],
        }
    if not isinstance(data, dict):
        return {
            "status": "invalid",
            "semantic_matches": [],
            "frontier_chains": [],
            "rejects": [],
        }
    data.setdefault("status", "ok")
    data.setdefault("semantic_matches", [])
    data.setdefault("frontier_chains", [])
    data.setdefault("rejects", [])
    return data


def _fuse_scan_matches(
    section_scores: list[dict[str, Any]],
    semantic_scan: dict[str, Any],
) -> list[dict[str, Any]]:
    """Fuse deterministic matches with semantic model matches."""
    by_section = {str(item.get("section", "")): item for item in section_scores}
    fused: list[dict[str, Any]] = []
    seen: set[str] = set()
    semantic_rows = [
        item for item in semantic_scan.get("semantic_matches", [])
        if isinstance(item, dict)
    ]
    semantic_status = str(semantic_scan.get("status", ""))
    semantic_authoritative = semantic_status == "ok" and bool(semantic_rows)

    # If Stage S+ failed or was skipped, keep the deterministic recall pass as
    # a fallback.  If Stage S+ succeeds, require semantic evidence instead of
    # accepting vocabulary matches blindly.
    if not semantic_authoritative:
        for item in section_scores:
            if item.get("match"):
                copy = dict(item)
                copy["match_source"] = "python_fallback"
                fused.append(copy)
                seen.add(str(item.get("section", "")))

    rejected_sections = {
        str(item.get("section", "")).strip()
        for item in semantic_scan.get("rejects", [])
        if isinstance(item, dict)
    }

    for raw in semantic_rows:
        section = str(raw.get("section", "")).strip()
        if section in rejected_sections:
            continue
        if not section or section not in by_section:
            continue
        mechanism = str(raw.get("mechanism", "")).strip()
        role = str(raw.get("theorem_chain_role", "")).strip()
        reason = str(raw.get("reason", "")).strip()
        try:
            semantic_score = float(raw.get("semantic_score", 0))
        except (TypeError, ValueError):
            semantic_score = 0.0
        if semantic_score < SEMANTIC_SCAN_ACCEPT_THRESHOLD:
            continue
        if not (mechanism and role and reason):
            continue
        base = dict(by_section[section])
        rel = str(raw.get("tex_file") or base.get("tex_file") or "")
        if rel:
            path = _scan_tex_path(rel)
            if path and path.exists():
                base["tex_file"] = path.relative_to(CORE_BODY).as_posix()
        base["semantic_score"] = round(max(0.0, min(1.0, semantic_score)), 4)
        base["semantic_reason"] = reason
        base["bad_example_mechanism"] = mechanism
        base["theorem_chain_role"] = role
        base["required_context_labels"] = raw.get("required_context_labels", [])
        base["match"] = True
        base["match_source"] = (
            "semantic" if semantic_authoritative else "python_fallback+semantic"
        )
        base["score"] = round(max(float(base.get("score", 0)), base["semantic_score"]), 4)
        if section in seen:
            fused = [
                base if str(existing.get("section", "")) == section else existing
                for existing in fused
            ]
        else:
            fused.append(base)
            seen.add(section)

    fused.sort(
        key=lambda item: (
            float(item.get("semantic_score", item.get("score", 0))),
            float(item.get("score", 0)),
        ),
        reverse=True,
    )
    return fused


def run_stage_s(state: DistillState, dry_run: bool = False) -> bool:
    """Run Stage S deterministic router matching over core LaTeX files.

    Scoring is section-level: triggers are aggregated across all .tex
    files within each top-level section directory.  Python matching is a
    deterministic recall pass; Stage S+ then lets Codex semantically rerank
    those candidates before writeback target selection.
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
    deterministic_matches = [item for item in section_scores if item["match"]]
    global_evidence_pack = _build_global_evidence_pack(raw_research, section_scores)
    _write_artifact_json(state, "global_evidence_pack.json", global_evidence_pack)
    semantic_scan = _semantic_scan(
        state,
        raw_research,
        section_scores,
        global_evidence_pack,
        dry_run=dry_run,
    )
    matches = _fuse_scan_matches(section_scores, semantic_scan)
    for item in matches:
        logger.info(
            "  matched section=%s source=%s score=%.4f coverage=%.4f triggers=%s",
            item["section"],
            item.get("match_source", "python"),
            item["score"],
            item["coverage"],
            item["unique_triggers"][:5],
        )
    output = {
        "mathematician": state.name,
        "trigger_count": len(triggers),
        "triggers": triggers,
        "matches": matches,
        "deterministic_matches": deterministic_matches,
        "semantic_scan": semantic_scan,
        "global_evidence_pack": {
            "artifact": "global_evidence_pack.json",
            "claim_count": len(global_evidence_pack.get("high_signal_claims", [])),
            "interface_count": len(global_evidence_pack.get("frontier_interfaces", [])),
            "distillation_claim_count": len(
                global_evidence_pack.get("existing_distillation_claims", [])
            ),
        },
        "all_sections": section_scores,
    }
    _write_artifact_json(state, "section_matches.json", output)
    _invalidate_after_stage_s(state)
    state.current_stage = "G"
    state.round_number += 1
    save_state(state)
    logger.info(
        "Stage S completed with %d fused section matches (%d deterministic, of %d sections)",
        len(matches),
        len(deterministic_matches),
        len(section_scores),
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
        "frontier_chains": matches.get("semantic_scan", {}).get("frontier_chains", []),
        "coverage_debts": [
            {
                "family": item.get("name", ""),
                "missing_mechanism": "dry-run family has not been proved",
                "target_sections": item.get("target_sections", []),
                "reason": "dry-run payload records coverage debt without claiming closure",
            }
            for item in raw.get("theorem_families", [])
        ],
        "closure_criteria": [
            "All theorem families have accepted writebacks and no active coverage debts remain."
        ],
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
    if not isinstance(data.get("frontier_chains", []), list):
        errors.append("frontier_chains must be a list")
    if not isinstance(data.get("coverage_debts", []), list):
        errors.append("coverage_debts must be a list")
    if not isinstance(data.get("closure_criteria", []), list):
        errors.append("closure_criteria must be a list")
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
            response = _codex_exec_with_infra_retries(
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
            _invalidate_after_stage_g(state)
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


def _is_wrapper_tex_file(path: Path) -> bool:
    """Return true for subfile/input routing files that are unsafe writeback targets."""
    try:
        text = read_text(path)
    except OSError:
        return False
    input_count = len(re.findall(r"\\(?:input|subfile)\{", text))
    if path.name == "main.tex":
        return input_count > 0
    if path.name.startswith("sec__") and input_count >= 3:
        return True
    return False


def _target_priority(path: Path, context: Optional[dict[str, Any]] = None) -> tuple[int, int, int, int, int, str]:
    """Rank concrete body files for theorem writeback targeting."""
    try:
        text = read_text(path)
    except OSError:
        text = ""
    labels = _unique_strings((context or {}).get("required_context_labels", []))
    label_hits = sum(1 for label in labels if label and label in text)
    claim_hits = len(CLAIM_ENV_RE.findall(text))
    name = path.name
    section_file = int(name.startswith("sec__"))
    subsection_file = int(name.startswith(("subsec__", "subsubsec__")))
    body_size = min(len(text), 100000)
    rel = path.relative_to(CORE_BODY).as_posix()
    return (label_hits, claim_hits, section_file, subsection_file, body_size, rel)


def _choose_writeback_target(
    candidates: list[Path],
    context: Optional[dict[str, Any]] = None,
) -> Optional[Path]:
    """Choose the best non-wrapper concrete theorem body file."""
    targets = _choose_writeback_targets(candidates, context=context, limit=1)
    return targets[0] if targets else None


def _choose_writeback_targets(
    candidates: list[Path],
    context: Optional[dict[str, Any]] = None,
    limit: int = 1,
) -> list[Path]:
    """Choose the best non-wrapper concrete theorem body files."""
    usable = []
    seen = set()
    for candidate in candidates:
        path = candidate.resolve()
        if path in seen:
            continue
        seen.add(path)
        if not path.exists() or path.suffix != ".tex":
            continue
        try:
            path.relative_to(CORE_BODY.resolve())
        except ValueError:
            continue
        if _is_wrapper_tex_file(path):
            continue
        try:
            text = read_text(path)
        except OSError:
            continue
        if not CLAIM_ENV_RE.search(text):
            continue
        base_lines = len(text.splitlines())
        if base_lines >= WRITEBACK_LINE_LIMIT - WRITEBACK_TARGET_LINE_HEADROOM:
            continue
        usable.append(path)
    if not usable:
        return []
    ranked = sorted(usable, key=lambda p: _target_priority(p, context), reverse=True)
    return ranked[: max(1, limit)]


def _target_file_descriptor(section: str, path: Path) -> dict[str, Any]:
    """Return a prompt-facing descriptor with the remaining line budget."""
    rel = path.relative_to(CORE_BODY).as_posix()
    try:
        current_lines = len(read_text(path).splitlines())
    except OSError:
        current_lines = 0
    remaining = max(0, WRITEBACK_LINE_LIMIT - 1 - current_lines)
    return {
        "section": section,
        "tex_file": rel,
        "current_lines": current_lines,
        "line_limit_exclusive": WRITEBACK_LINE_LIMIT,
        "remaining_lines_before_gate": remaining,
        "recommended_total_insert_lines": max(0, remaining - 8),
    }


def _match_candidate_paths(item: dict[str, Any]) -> list[Path]:
    """Collect concrete file candidates from a semantic match row."""
    candidates = []
    rel = str(item.get("tex_file", ""))
    path = _resolve_core_tex_path(rel)
    if path and path.exists():
        candidates.append(path)
    for row in item.get("top_files", []):
        rel = str(row.get("tex_file", ""))
        path = _resolve_core_tex_path(rel)
        if path and path.exists():
            candidates.append(path)
    return candidates


def _select_section_writeback_targets(
    section: str,
    matches: dict[str, Any],
    limit: int = 1,
) -> list[dict[str, Any]]:
    """Select concrete theorem body files for one section slug."""
    for item in matches.get("matches", []):
        if item.get("section") != section:
            continue
        paths = _choose_writeback_targets(_match_candidate_paths(item), item, limit=limit)
        if paths:
            return [_target_file_descriptor(section, path) for path in paths]
    section_dir = CORE_BODY / section
    if not section_dir.exists():
        return []
    paths = _choose_writeback_targets(sorted(section_dir.rglob("*.tex")), limit=limit)
    return [_target_file_descriptor(section, path) for path in paths]


def _select_target_files(
    payload: dict[str, Any],
    matches: dict[str, Any],
) -> list[dict[str, Any]]:
    """Select concrete target `.tex` files for writeback prompting."""
    selected = []
    seen = set()
    targets = _payload_targets(payload, matches)
    match_rows = matches.get("matches", [])
    for target in targets:
        selected_for_target = False
        if target.endswith(".tex"):
            path = _resolve_core_tex_path(target)
            if path and path.exists() and not _is_wrapper_tex_file(path):
                rel = path.relative_to(CORE_BODY).as_posix()
                selected.append(_target_file_descriptor(rel.split("/")[0], path))
                seen.add(rel)
                selected_for_target = True
            continue
        for item in match_rows:
            if item.get("section") != target:
                continue
            limit = 2 if _unique_strings(item.get("required_context_labels", [])) else 1
            for selected_target in _select_section_writeback_targets(target, matches, limit=limit):
                rel = selected_target["tex_file"]
                if rel in seen:
                    continue
                selected.append(selected_target)
                seen.add(rel)
                selected_for_target = True
            if selected_for_target:
                break
        if selected_for_target:
            continue
        for selected_target in _select_section_writeback_targets(target, matches):
            rel = selected_target["tex_file"]
            if rel not in seen:
                selected.append(selected_target)
                seen.add(rel)
    return selected[:MAX_WRITEBACK_TARGET_FILES]


def _collect_section_contexts(
    targets: list[dict[str, Any]],
    *,
    max_chars_per_file: int = 16000,
) -> str:
    """Read target LaTeX files and format them as prompt context."""
    chunks = []
    for target in targets:
        rel = target["tex_file"]
        path = _resolve_core_tex_path(rel)
        if not path or not path.exists():
            continue
        text = read_text(path)
        if len(text) > max_chars_per_file:
            text = text[:max_chars_per_file] + "\n% [context truncated by distill.py]\n"
        chunks.append(f"--- {rel} ---\n{text}")
    return "\n\n".join(chunks)


def _collect_oracle_deepening_contexts(targets: list[dict[str, Any]]) -> str:
    """Collect a compact target context for browser-based Oracle prompts."""
    return _collect_section_contexts(
        targets,
        max_chars_per_file=ORACLE_DEEPENING_SECTION_CONTEXT_CHARS,
    )


def _dry_writebacks(targets: list[dict[str, Any]], name: str) -> list[dict[str, str]]:
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


def _next_distill_result_number() -> int:
    """Estimate the next global distillation result number from existing labels."""
    if not CORE_BODY.exists():
        return 1
    count = 0
    for tex_file in CORE_BODY.rglob("*.tex"):
        if not tex_file.is_file():
            continue
        try:
            count += len(re.findall(r"\\label\{[^}]*distill[-:]", read_text(tex_file)))
        except OSError:
            continue
    return count + 1


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


def _validate_writebacks(
    writebacks: Any,
    allowed_tex_files: Optional[set[str]] = None,
) -> tuple[list[dict[str, Any]], list[str]]:
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
        if allowed_tex_files is not None and rel not in allowed_tex_files:
            errors.append(
                f"Item {index} targets {rel}, which was not provided in Target files"
            )
            continue
        path = _resolve_core_tex_path(rel)
        if not path or not path.exists():
            errors.append(f"Item {index} target file not found under core body: {rel}")
            continue
        if _is_wrapper_tex_file(path):
            errors.append(
                f"Item {index} targets wrapper/routing file instead of theorem body: {rel}"
            )
            continue
        label = str(item["label"]).strip()
        content = str(item["content"]).strip()
        if label in labels:
            errors.append(f"Duplicate proposed label: {label}")
            continue
        labels.add(label)
        if "\\documentclass" in content or "\\begin{document}" in content:
            errors.append(f"Item {index} contains document-level LaTeX")
        if SECTIONING_COMMAND_RE.search(content):
            errors.append(
                f"Item {index} opens a sectioning command; integrate into an existing concrete section instead"
            )
        if "\\endinput" in content:
            errors.append(
                f"Item {index} emits \\endinput; the application planner handles insertion before it"
            )
        if not CJK_RE.search(content):
            errors.append(
                f"Item {index} is not written as Chinese main-paper academic prose"
            )
        trace = KILLO_GOLDEN_TRACE_RE.search(content)
        if trace:
            errors.append(
                f"Item {index} contains visible patch/log wording forbidden by killo-golden: {trace.group(0)}"
            )
        metadata = PIPELINE_METADATA_RE.search(content)
        if metadata:
            errors.append(
                f"Item {index} contains pipeline metadata forbidden in paper LaTeX: {metadata.group(0)}"
            )
        ordinal = MANUAL_RESULT_ORDINAL_RE.search(content)
        if ordinal:
            errors.append(
                f"Item {index} hard-codes unstable human-facing result ordinal: {ordinal.group(0)}"
            )
        if label not in content:
            errors.append(f"Item {index} content does not contain label {label}")
        existing_text = read_text(path)
        existing_without_distill = _DISTILL_BLOCK_RE.sub("", existing_text)
        if re.search(rf"\\label\{{{re.escape(label)}\}}", existing_without_distill):
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
    cleaned = str(response or "").strip()
    lower = cleaned.lower()
    unavailable_markers = (
        "you've hit your limit",
        "you have hit your limit",
        "usage limit",
        "rate limit",
        "try again later",
        "(timeout)",
        "(start-failed)",
        "dry run -- no output",
    )
    marker_unavailable = any(marker in lower for marker in unavailable_markers)
    if not cleaned or marker_unavailable:
        return {
            "score": 0,
            "verdict": "unavailable",
            "issues": [cleaned[:1000] or "Reviewer returned no output"],
            "required_changes": [],
            "unavailable": True,
            "retryable": not marker_unavailable,
        }
    try:
        data = _extract_json(cleaned)
    except (ValueError, json.JSONDecodeError):
        return {
            "score": 0,
            "verdict": "unavailable",
            "issues": [
                "Reviewer returned no parseable score JSON",
                cleaned[:1000],
            ],
            "required_changes": [],
            "unavailable": True,
            "retryable": True,
        }
    if not isinstance(data, dict):
        return {
            "score": 0,
            "verdict": "unavailable",
            "issues": ["Reviewer returned non-object JSON"],
            "required_changes": [],
            "unavailable": True,
            "retryable": True,
        }
    try:
        score = int(float(data.get("score", 1)))
    except (TypeError, ValueError):
        score = 1
    data["score"] = max(1, min(10, score))
    data.setdefault("verdict", "revise" if data["score"] < 7 else "accept")
    data.setdefault("issues", [])
    data.setdefault("required_changes", [])
    data.setdefault("unavailable", False)
    data.setdefault("retryable", False)
    return data


def _codex_score(
    state: DistillState,
    writebacks: list[dict[str, Any]],
    payload: dict[str, Any],
    section_contexts: str,
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
        section_contexts=section_contexts,
        score_schema=_score_schema(),
    )
    for attempt in range(1, 3):
        response = _codex_exec_with_infra_retries(
            prompt,
            work_dir=CORE_BODY,
            timeout_seconds=900,
            dry_run=False,
            log_tag=f"{_slugify(state.name)}_W_review_codex_a{attempt}",
        )
        result = _parse_score_response(response)
        if result.get("score", 0) > 0:
            return result
        if not result.get("retryable"):
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
        if result.get("score", 0) > 0:
            return result
        if not result.get("retryable"):
            return result
        logger.warning(
            "Claude review attempt %d: empty/unparseable, retrying", attempt
        )
    return _parse_score_response(response)


def _oracle_deepening_quality_issues(data: Any, response: str) -> list[str]:
    """Return issues that make Oracle deepening unusable as research context."""
    if not isinstance(data, dict):
        return ["Oracle deepening did not return a JSON object"]
    status = str(data.get("status", "")).strip().lower()
    if status in {"parse_failed", "invalid", "unavailable", "error"}:
        return [f"Oracle deepening status is {status or 'missing'}"]
    if status == "ok_raw":
        return _oracle_raw_research_quality_issues(
            str(data.get("raw_research_text", response or ""))
        )
    chain = data.get("main_theorem_chain", [])
    if not isinstance(chain, list) or not chain:
        return ["Oracle deepening has no main_theorem_chain entries"]
    substantive = 0
    for item in chain:
        if not isinstance(item, dict):
            continue
        title = str(item.get("proposed_title", "")).strip()
        conclusion = str(item.get("conclusion", "")).strip()
        proof_spine = item.get("proof_spine", [])
        if title and conclusion and isinstance(proof_spine, list) and proof_spine:
            substantive += 1
    if substantive == 0:
        return ["Oracle deepening has no substantive theorem-chain entry"]
    if len(response.strip()) < 1200:
        return ["Oracle deepening response is too short to be reliable"]
    return []


def _oracle_raw_research_quality_issues(response: str) -> list[str]:
    """Return issues for free-form Oracle research text."""
    text = (response or "").strip()
    if len(text) < 1200:
        return ["Oracle raw research response is too short to be reliable"]
    bundle_markers = (
        "markdown writeback bundle",
        "raw tex bundle",
        "insertion-ready writebacks",
        "\nfiles:\n",
    )
    lowered = text.lower()
    if any(marker in lowered for marker in bundle_markers):
        return ["Oracle raw response describes bundles/files instead of research results"]
    result_markers = (
        "\\begin{theorem",
        "\\begin{proposition",
        "\\begin{lemma",
        "theorem",
        "proposition",
        "lemma",
        "\u5b9a\u7406",
        "\u547d\u9898",
        "\u5f15\u7406",
        "\u8bc1\u660e",
        "proof",
    )
    if not any(marker in lowered or marker in text for marker in result_markers):
        return ["Oracle raw response has no theorem/proposition/proof markers"]
    return []


def _raw_oracle_deepening_context(response: str, error: str = "") -> dict[str, Any]:
    """Wrap free-form Oracle research so Codex can use it as context."""
    data: dict[str, Any] = {
        "status": "ok_raw",
        "format": "free_form_research_text",
        "raw_research_text": response.strip(),
        "main_theorem_chain": [],
        "codex_writeback_instructions": [
            "Use raw_research_text as expansion-oriented mathematical context.",
            "Do not assume it is already verified paper text; extract only locally provable claims.",
        ],
    }
    if error:
        data["parse_note"] = error
    return data


def _has_usable_oracle_deepening(data: Any) -> bool:
    """Return true for cached Oracle data that should not be overwritten."""
    if not isinstance(data, dict):
        return False
    status = str(data.get("status", "")).strip().lower()
    if status in {"parse_failed", "invalid", "unavailable", "error"}:
        return False
    if status == "ok_raw":
        return not _oracle_raw_research_quality_issues(
            str(data.get("raw_research_text", ""))
        )
    chain = data.get("main_theorem_chain", [])
    if not isinstance(chain, list) or not chain:
        return False
    for item in chain:
        if not isinstance(item, dict):
            continue
        proof = item.get("proof_spine", [])
        has_proof = isinstance(proof, list) and len([x for x in proof if str(x).strip()]) >= 3
        if item.get("conclusion") and (has_proof or item.get("minimal_hypotheses")):
            return True
    return False


def _recover_oracle_deepening_from_done(
    state: DistillState,
    depth_cycle: int,
) -> tuple[dict[str, Any], Path, str] | None:
    """Recover a valid Oracle deepening JSON object from durable done files."""
    prefix = f"{_slugify(state.name)}_W_oracle_deepen_cycle{depth_cycle}"
    if not ORACLE_DONE_DIR.exists():
        return None
    candidates = sorted(
        ORACLE_DONE_DIR.glob(f"{prefix}*.md"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    for path in candidates:
        try:
            response = _strip_oracle_response_metadata(read_text(path)).strip()
        except OSError:
            continue
        if not response:
            continue
        try:
            parsed = _extract_json(response)
        except (ValueError, json.JSONDecodeError):
            raw_data = _raw_oracle_deepening_context(response, "No parseable JSON found")
            if not _oracle_deepening_quality_issues(raw_data, response):
                return raw_data, path, response
            continue
        if not isinstance(parsed, dict):
            raw_data = _raw_oracle_deepening_context(
                response,
                "Parsed JSON was not an object",
            )
            if not _oracle_deepening_quality_issues(raw_data, response):
                return raw_data, path, response
            continue
        parsed.setdefault("status", "ok")
        parsed.setdefault("main_theorem_chain", [])
        if not _oracle_deepening_quality_issues(parsed, response):
            return parsed, path, response
    return None


def _persist_recovered_oracle_deepening(
    state: DistillState,
    data: dict[str, Any],
    source_path: Path,
    response: str,
    focused_family: Optional[dict[str, Any]],
) -> None:
    """Persist a recovered Oracle deepening result into state artifacts."""
    _write_artifact_json(state, f"oracle_deepening_cycle{state.depth_cycle}.json", data)
    _write_artifact_json(
        state,
        f"oracle_deepening_cycle{state.depth_cycle}_attempts.json",
        [
            {
                "attempt": "recovered",
                "status": data.get("status", "ok"),
                "response_length": len(response),
                "source": str(source_path.relative_to(REPO_ROOT)),
                "issues": [],
            }
        ],
    )
    metadata = {
        "task_id": source_path.stem,
        "timestamp": _now_iso(),
        "response_length": len(response),
        "source": str(source_path.relative_to(REPO_ROOT)),
        "recovered": True,
    }
    write_text(
        _artifact_path(state, f"W_oracle_deepen_cycle{state.depth_cycle}_oracle_response.md"),
        f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
    )
    _upsert_distillation_memory(
        _memory_entries_from_oracle_sidecar(state, data, focused_family)
    )


def _oracle_deepening_research(
    state: DistillState,
    payload: dict[str, Any],
    raw_research: dict[str, Any],
    focused_family: Optional[dict[str, Any]],
    targets: list[dict[str, Any]],
    section_contexts: str,
    global_evidence_pack: dict[str, Any],
    prior_feedback_block: str,
    dry_run: bool,
    oracle_timeout: int,
    oracle_model: str,
    oracle_pdf: Optional[Path],
) -> dict[str, Any]:
    """Ask ChatGPT Oracle for expansion-oriented deep reasoning context."""
    if dry_run:
        return {"status": "dry_run", "main_theorem_chain": []}
    cached = _read_artifact_json_or_none(
        state,
        f"oracle_deepening_cycle{state.depth_cycle}.json",
    )
    if _has_usable_oracle_deepening(cached):
        logger.info(
            "Reusing cached Oracle deepening for cycle %d",
            state.depth_cycle,
        )
        return cached
    recovered = _recover_oracle_deepening_from_done(state, state.depth_cycle)
    if recovered:
        data, source_path, response = recovered
        logger.info(
            "Recovered Oracle deepening for cycle %d from %s",
            state.depth_cycle,
            source_path,
        )
        _persist_recovered_oracle_deepening(
            state,
            data,
            source_path,
            response,
            focused_family,
        )
        return data
    family = focused_family or {
        "name": "initial writeback payload",
        "key_results": payload.get("frontier_chains", []),
        "target_sections": payload.get("primary_targets", []),
    }
    blocked = _read_artifact_json_or_none(state, "blocked.json") or {}
    oracle_payload = _oracle_payload_summary(payload, focused_family)
    oracle_global_evidence_pack = _oracle_relevant_evidence_pack(
        global_evidence_pack,
        focused_family,
        targets,
    )
    base_prompt = _load_prompt("oracle_deepening").format(
        mathematician=state.name,
        current_datetime=datetime.now().astimezone().isoformat(timespec="seconds"),
        depth_cycle=state.depth_cycle,
        family_name=family.get("name", ""),
        key_results=_json_block(family.get("key_results", [])),
        method_operators=_json_block(raw_research.get("method_operators", [])),
        payload=_json_block(oracle_payload),
        targets=_json_block(targets),
        section_contexts=section_contexts,
        global_evidence_pack=_json_block(oracle_global_evidence_pack),
        prior_feedback=prior_feedback_block or "none",
        blocked_context=_json_block(blocked),
        completed_families=", ".join(state.completed_families or ["none"]),
        deep_research_directive=_deep_research_directive(),
        schema=_oracle_deepening_schema(),
    )
    attempts: list[dict[str, Any]] = []
    last_data: dict[str, Any] = {"status": "unavailable", "main_theorem_chain": []}
    retry_suffix = ""
    for attempt in range(1, 3):
        prompt = base_prompt + retry_suffix
        response = chatgpt_oracle_exec(
            state,
            prompt,
            log_tag=f"W_oracle_deepen_cycle{state.depth_cycle}_a{attempt}",
            timeout_seconds=oracle_timeout,
            model=oracle_model,
            pdf_path=oracle_pdf,
            dry_run=False,
        )
        if not response:
            data: dict[str, Any] = {"status": "unavailable", "main_theorem_chain": []}
            issues = ["Oracle returned no response"]
        else:
            try:
                parsed = _extract_json(response)
            except (ValueError, json.JSONDecodeError) as exc:
                parsed = _raw_oracle_deepening_context(response, str(exc))
            if isinstance(parsed, dict):
                data = parsed
            else:
                data = _raw_oracle_deepening_context(
                    response,
                    "Parsed JSON was not an object",
                )
            data.setdefault("status", "ok")
            data.setdefault("main_theorem_chain", [])
            issues = _oracle_deepening_quality_issues(data, response)
        attempts.append(
            {
                "attempt": attempt,
                "status": data.get("status"),
                "response_length": len(response or ""),
                "issues": issues,
            }
        )
        last_data = data
        if not issues:
            _write_artifact_json(
                state,
                f"oracle_deepening_cycle{state.depth_cycle}.json",
                data,
            )
            _write_artifact_json(
                state,
                f"oracle_deepening_cycle{state.depth_cycle}_attempts.json",
                attempts,
            )
            _upsert_distillation_memory(
                _memory_entries_from_oracle_sidecar(state, data, focused_family)
            )
            return data
        logger.warning(
            "Oracle deepening attempt %d unusable: %s",
            attempt,
            "; ".join(issues),
        )
        if not response:
            logger.warning(
                "Oracle deepening produced no response; skipping retry because Oracle is optional"
            )
            break
        retry_suffix = (
            "\n\nPREVIOUS ORACLE RESPONSE WAS INVALID FOR THIS PIPELINE: "
            + "; ".join(issues)
            + "\nReturn a single valid JSON object matching the schema. "
            + "Do not mention bundles, files, markdown, downloads, or prose summaries. "
            + "If blocked, return status=\"blocked\" with a nonempty main_theorem_chain "
            + "containing the narrowest conditional theorem chain you can defend."
        )
    recovered = _recover_oracle_deepening_from_done(state, state.depth_cycle)
    if recovered:
        data, source_path, response = recovered
        logger.info(
            "Recovered Oracle deepening for cycle %d after failed live attempts from %s",
            state.depth_cycle,
            source_path,
        )
        _persist_recovered_oracle_deepening(
            state,
            data,
            source_path,
            response,
            focused_family,
        )
        return data
    fallback = {
        "status": "unavailable",
        "main_theorem_chain": [],
        "issues": [
            "Oracle deepening did not produce valid structured research context after retries"
        ],
        "last_response": last_data,
        "attempts": attempts,
    }
    _write_artifact_json(state, f"oracle_deepening_cycle{state.depth_cycle}.json", fallback)
    _write_artifact_json(state, f"oracle_deepening_cycle{state.depth_cycle}_attempts.json", attempts)
    return fallback


def _score_required_changes(review: dict[str, Any]) -> list[str]:
    """Return nonempty required changes from a reviewer result."""
    raw = review.get("required_changes", [])
    if isinstance(raw, list):
        return [str(item).strip() for item in raw if str(item).strip()]
    if isinstance(raw, str) and raw.strip():
        return [raw.strip()]
    return []


def _combine_review_scores(scores: list[int]) -> int:
    """Combine one or two reviewer scores using the existing lenient rule."""
    if not scores:
        return 0
    if len(scores) == 1:
        return scores[0]
    low = min(scores)
    high = max(scores)
    if low >= SCORE_PASS_THRESHOLD:
        return low
    if high >= SCORE_PASS_THRESHOLD and low >= 4:
        return high
    if high >= SCORE_PASS_THRESHOLD and low < 4:
        return 6
    return high


def _compact_review_feedback(review: dict[str, Any], max_chars: int = 1600) -> str:
    """Build a durable one-line summary of actionable review feedback."""
    if not isinstance(review, dict):
        return ""
    backend = str(review.get("review_backend", "review")).strip() or "review"
    final_score = review.get("minimum_score", "?")
    parts = [
        f"review gate below {SCORE_PASS_THRESHOLD} "
        f"(backend={backend}, final={final_score})"
    ]
    for name in ("codex", "claude", "oracle"):
        reviewer = review.get(name)
        if not isinstance(reviewer, dict) or reviewer.get("unavailable"):
            continue
        score = reviewer.get("score", "?")
        verdict = str(reviewer.get("verdict", "")).strip() or "missing"
        details = []
        for key, label in (
            ("issues", "issue"),
            ("required_changes", "required_change"),
        ):
            raw_items = reviewer.get(key, [])
            if isinstance(raw_items, str):
                raw_items = [raw_items]
            if not isinstance(raw_items, list):
                continue
            for item in raw_items[:3]:
                text = re.sub(r"\s+", " ", str(item)).strip()
                if text:
                    details.append(f"{label}: {text}")
        if details:
            parts.append(
                f"{name} score={score} verdict={verdict}: "
                + " | ".join(details[:4])
            )
        else:
            parts.append(f"{name} score={score} verdict={verdict}")
    summary = "; ".join(parts)
    if len(summary) > max_chars:
        return summary[: max_chars - 3].rstrip() + "..."
    return summary


def _review_writebacks(
    state: DistillState,
    writebacks: list[dict[str, Any]],
    payload: dict[str, Any],
    section_contexts: str,
    dry_run: bool,
    review_backend: str = DEFAULT_REVIEW_BACKEND,
    oracle_timeout: int = DEFAULT_ORACLE_TIMEOUT,
    oracle_model: str = DEFAULT_ORACLE_MODEL,
    oracle_pdf: Optional[Path] = None,
) -> dict[str, Any]:
    """Run the configured review gate for writeback proposals.

    Uses parallel independent scoring. If one reviewer returns empty JSON,
    falls back to the other; if both empty, returns score 0 so the round
    retries.  Ported from oracle_pipeline.py A3+A4 parallel dual review.
    """
    if review_backend not in REVIEW_BACKENDS:
        review_backend = DEFAULT_REVIEW_BACKEND

    _unavailable_review = {
        "score": 0,
        "verdict": "unavailable",
        "issues": ["Reviewer not configured for this backend"],
        "required_changes": [],
        "unavailable": True,
        "retryable": False,
    }
    with ThreadPoolExecutor(max_workers=2) as executor:
        codex_future = None
        claude_future = None
        if review_backend == "claude":
            # Claude-only review: Codex generates, Claude reviews
            claude_future = executor.submit(
                _claude_score,
                state,
                writebacks,
                section_contexts,
                dry_run,
            )
        elif review_backend == "codex-claude":
            # Dual review: both Codex and Claude score in parallel
            codex_future = executor.submit(
                _codex_score,
                state,
                writebacks,
                payload,
                section_contexts,
                dry_run,
            )
            claude_future = executor.submit(
                _claude_score,
                state,
                writebacks,
                section_contexts,
                dry_run,
            )
        else:  # "codex"
            codex_future = executor.submit(
                _codex_score,
                state,
                writebacks,
                payload,
                section_contexts,
                dry_run,
            )
        codex_review = codex_future.result() if codex_future else dict(_unavailable_review)
        claude_review = claude_future.result() if claude_future else dict(_unavailable_review)

    codex_s = int(codex_review.get("score", 0) or 0)
    claude_s = int(claude_review.get("score", 0) or 0)
    codex_ok = codex_s > 0
    claude_ok = claude_s > 0
    named_reviews = []
    if codex_future is not None:
        named_reviews.append(("codex", codex_review))
    if claude_future is not None:
        named_reviews.append(("claude", claude_review))

    if review_backend == "claude":
        # Claude-only: score is Claude's score directly
        if claude_ok:
            final_score = claude_s
        else:
            logger.warning("Claude review unavailable in claude-only backend")
            final_score = 0
    elif review_backend == "codex":
        # Codex-only: score is Codex's score directly
        if codex_ok:
            final_score = codex_s
        else:
            logger.warning("Codex review unavailable in codex-only backend")
            final_score = 0
    elif codex_ok and claude_ok:
        # Dual review (codex-claude): lenient combination
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
        logger.warning("Claude review unavailable in dual backend, using codex=%d", codex_s)
        final_score = codex_s
    elif claude_ok:
        logger.warning("Codex review unavailable in dual backend, using claude=%d", claude_s)
        final_score = claude_s
    else:
        logger.warning("No configured reviewer returned usable JSON")
        final_score = 0

    # Detect FUNDAMENTAL depth issue: primary reviewer says "reject"
    if review_backend == "codex-claude":
        both_reject = (
            codex_ok
            and claude_ok
            and codex_review.get("verdict") == "reject"
            and claude_review.get("verdict") == "reject"
        )
    elif review_backend == "claude":
        both_reject = claude_ok and claude_review.get("verdict") == "reject"
    else:
        both_reject = codex_ok and codex_review.get("verdict") == "reject"
    available_reviews = [
        (name, review)
        for name, review in named_reviews
        if int(review.get("score", 0) or 0) > 0
    ]
    blockers = []
    for name, review in available_reviews:
        score = int(review.get("score", 0) or 0)
        verdict = str(review.get("verdict", "")).strip().lower()
        if score < SCORE_PASS_THRESHOLD:
            blockers.append(f"{name}: score {score} below threshold")
        elif verdict != "accept":
            blockers.append(f"{name}: verdict={verdict or 'missing'}")
        elif _score_required_changes(review):
            blockers.append(f"{name}: required_changes present")
    # Gate passes when primary reviewer(s) OK and score meets threshold
    if review_backend == "claude":
        gate_passed = bool(claude_ok and final_score >= SCORE_PASS_THRESHOLD and not blockers)
    else:
        gate_passed = bool(codex_ok and final_score >= SCORE_PASS_THRESHOLD and not blockers)

    logger.info(
        "Review gate: backend=%s codex=%d claude=%d final=%d passed=%s blockers=%s",
        review_backend,
        codex_s,
        claude_s,
        final_score,
        gate_passed,
        blockers[:3],
    )

    result = {
        "codex": codex_review,
        "claude": claude_review,
        "minimum_score": final_score,
        "gate_passed": gate_passed,
        "blocking_reviewers": blockers,
        "review_backend": review_backend,
        "both_reject": both_reject,
    }
    if not gate_passed:
        feedback_summary = _compact_review_feedback(result)
        if feedback_summary:
            logger.info("Review feedback summary: %s", feedback_summary)
    return result


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
    r"\n?% --- Distillation writeback(?:[:][^\n]*)? ---\n"
    r".*?% --- End distillation writeback ---\n?",
    re.DOTALL,
)


def _remove_conflicting_distill_blocks(text: str, labels: list[str]) -> str:
    """Remove only prior distillation blocks that contain incoming labels."""
    markers = [f"\\label{{{label}}}" for label in labels if label]
    if not markers:
        return text

    def replace(match: re.Match[str]) -> str:
        block = match.group(0)
        if any(marker in block for marker in markers):
            return "\n"
        return block

    return _DISTILL_BLOCK_RE.sub(replace, text)


def _plan_writeback_application(
    writebacks: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[str]]:
    """Prepare file-level writeback insertions without modifying files.

    Idempotent: prior distillation blocks are preserved unless they already
    contain one of the incoming labels, in which case only the conflicting
    block is replaced.
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

        # Build one distillation block per item so later replacements do not
        # delete unrelated writebacks in the same file.
        blocks = []
        for item in items:
            block_lines = ["", "% --- Distillation writeback ---"]
            block_lines.append(item["content"].strip())
            block_lines.append("")
            block_lines.append("% --- End distillation writeback ---")
            blocks.append("\n".join(block_lines).rstrip())
        insert_block = "\n".join(blocks).rstrip() + "\n"

        # Idempotent: only replace blocks containing incoming labels.
        base_text = _remove_conflicting_distill_blocks(
            old_text,
            [item["label"] for item in items],
        )

        position = _find_insert_position(base_text)
        prefix = base_text[:position].rstrip()
        suffix = base_text[position:].lstrip("\n")
        new_text = prefix + "\n" + insert_block
        if suffix:
            new_text += "\n" + suffix
        line_count = len(new_text.splitlines())
        if line_count >= WRITEBACK_LINE_LIMIT:
            errors.append(
                f"{rel} would have {line_count} lines, exceeding <{WRITEBACK_LINE_LIMIT} gate"
            )
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
    temp_dir = _make_temporary_directory(prefix="omega_distill_edit_")
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


def _append_writeback_ledger(
    state: DistillState,
    *,
    status: str,
    focused_family: Optional[dict[str, Any]],
    accepted_writebacks: list[dict[str, Any]],
    applied: list[dict[str, Any]],
    skipped: list[dict[str, Any]],
    review: dict[str, Any],
) -> list[dict[str, Any]]:
    """Append a durable cumulative writeback ledger entry."""
    path = _artifact_path(state, "writeback_ledger.json")
    if path.exists():
        try:
            ledger = read_json(path)
        except (OSError, json.JSONDecodeError):
            ledger = []
    else:
        ledger = []
    if not isinstance(ledger, list):
        ledger = []
    entry = {
        "updated_at": _now_iso(),
        "depth_cycle": state.depth_cycle,
        "family": focused_family.get("name") if focused_family else None,
        "status": status,
        "writebacks": [
            {
                "section": item.get("section"),
                "tex_file": item.get("tex_file"),
                "type": item.get("type"),
                "label": item.get("label"),
            }
            for item in accepted_writebacks
        ],
        "applied": applied,
        "skipped": skipped,
        "review": review,
    }
    ledger.append(entry)
    write_json(path, ledger)
    return ledger


def run_stage_w(
    state: DistillState,
    dry_run: bool = False,
    supervised: bool = True,
    review_backend: str = DEFAULT_REVIEW_BACKEND,
    oracle_deepening: bool = False,
    oracle_timeout: int = DEFAULT_ORACLE_TIMEOUT,
    oracle_model: str = DEFAULT_ORACLE_MODEL,
    oracle_pdf: Optional[Path] = None,
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
        family_sections = _unique_strings(focused_family.get("target_sections", []))
        family_section_set = set(family_sections)
        focused_targets = [t for t in targets if t["section"] in family_section_set]
        present_sections = {t["section"] for t in focused_targets}
        for sec in family_sections:
            if sec in present_sections:
                continue
            additions = _select_section_writeback_targets(sec, matches)
            focused_targets.extend(additions)
            if additions:
                present_sections.add(sec)
        if focused_targets:
            targets = focused_targets

    if not targets:
        logger.error("Stage W could not select target files")
        return False
    section_contexts = _collect_section_contexts(
        targets,
        max_chars_per_file=(
            ORACLE_SECTION_CONTEXT_CHARS if oracle_deepening else 16000
        ),
    )
    global_evidence_pack = _global_evidence_for_state(state)
    prior_feedback_block = _build_prior_feedback_block(state)
    family_specific_contract = _family_specific_deepening_contract(focused_family)
    oracle_deepening_context: dict[str, Any] = {"status": "disabled"}
    if oracle_deepening:
        oracle_section_contexts = _collect_oracle_deepening_contexts(targets)
        oracle_deepening_context = _oracle_deepening_research(
            state,
            payload,
            raw_research,
            focused_family,
            targets,
            oracle_section_contexts,
            global_evidence_pack,
            prior_feedback_block,
            dry_run,
            oracle_timeout,
            oracle_model,
            oracle_pdf,
        )
    feedback = ""
    attempts = []
    accepted_writebacks: list[dict[str, Any]] = []
    accepted_review: dict[str, Any] = {}
    accepted_plan: list[dict[str, Any]] = []
    deep_rounds = 0
    for attempt in range(1, MAX_W_ROUNDS + 1):
        if dry_run:
            raw_writebacks = _dry_writebacks(targets, state.name)
        else:
            if focused_family:
                prompt = _load_prompt("deepen").format(
                    mathematician=state.name,
                    depth_cycle=state.depth_cycle,
                    family_name=focused_family.get("name", ""),
                    current_datetime=datetime.now().astimezone().isoformat(timespec="seconds"),
                    next_number=_next_distill_result_number(),
                    key_results="\n".join(
                        f"- {item}" for item in focused_family.get("key_results", [])
                    ),
                    method_operators=_json_block(raw_research.get("method_operators", [])),
                    targets=_json_block(targets),
                    section_contexts=section_contexts,
                    global_evidence_pack=_json_block(global_evidence_pack),
                    oracle_deepening_context=_json_block(oracle_deepening_context),
                    completed_families=", ".join(state.completed_families or ["none"]),
                    deep_research_directive=_deep_research_directive(),
                    schema=_writeback_schema(),
                    source_slug=_slugify(state.name),
                    family_slug=_slugify(str(focused_family.get("name", "family"))),
                )
            else:
                prompt = _load_prompt("writeback").format(
                    mathematician=state.name,
                    payload=_json_block(payload),
                    targets=_json_block(targets),
                    section_contexts=section_contexts,
                    global_evidence_pack=_json_block(global_evidence_pack),
                    oracle_deepening_context=_json_block(oracle_deepening_context),
                    schema=_writeback_schema(),
                )
            if prior_feedback_block:
                prompt += "\n\n" + prior_feedback_block
            if family_specific_contract:
                prompt += "\n\n" + family_specific_contract
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
            if low_rounds >= 3:
                prompt += (
                    "\n\nLAST-MILE CONSERVATIVE PROOF MODE:\n"
                    "- Prior attempts repeatedly overclaimed. Produce only claims whose "
                    "hypotheses explicitly include every auxiliary predicate, carrier, "
                    "tag, closure operation, readout, and budget used in the proof.\n"
                    "- Prefer 1-2 self-contained conditional finite audit lemmas over "
                    "broad multi-target coverage. Omit a target file if you cannot type "
                    "all of its symbols locally.\n"
                    "- Do not use theorem titles or dependency status words suggesting "
                    "closure, intrinsic dichotomy, or full Wang-Zahl extraction unless "
                    "you prove every branch. Use construction, conditional audit, or "
                    "conditional rigidity language.\n"
                    "- For grain/prism families, include slab, sector, thick-prism or "
                    "container-budget, thin-prism, and holonomy/Frostman/budget branches "
                    "only as explicitly defined finite certificate alternatives. If a "
                    "branch is not proved, state it as an assumption or omit the claim "
                    "that the family is closed.\n"
                    "- If a reviewer called a clause vacuous or false, remove that clause "
                    "rather than rephrasing it.\n"
                )
            w_timeout = 2400 if low_rounds >= 2 else 1800
            response = _codex_exec_with_infra_retries(
                prompt,
                work_dir=CORE_BODY,
                timeout_seconds=w_timeout,
                dry_run=False,
                log_tag=f"{_slugify(state.name)}_W_attempt{attempt}",
            )
            try:
                raw_writebacks = _extract_json(response)
            except (ValueError, json.JSONDecodeError) as exc:
                feedback = f"Could not parse writeback JSON: {exc}"
                attempts.append({"attempt": attempt, "errors": [feedback]})
                state.prior_feedback.append(f"W attempt {attempt}: {feedback}")
                save_state(state)
                continue

        allowed_tex_files = {str(target.get("tex_file", "")) for target in targets}
        writebacks, validation_errors = _validate_writebacks(
            raw_writebacks,
            allowed_tex_files=allowed_tex_files,
        )
        if validation_errors:
            feedback = "; ".join(validation_errors)
            attempts.append({"attempt": attempt, "errors": validation_errors})
            state.prior_feedback.append(f"W attempt {attempt}: {feedback}")
            save_state(state)
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

        candidate_plan, plan_errors = _plan_writeback_application(writebacks)
        if plan_errors:
            feedback = "Application plan failed: " + "; ".join(plan_errors)
            attempts.append({"attempt": attempt, "plan_errors": plan_errors})
            state.prior_feedback.append(f"W attempt {attempt}: {feedback}")
            save_state(state)
            continue

        review = _review_writebacks(
            state,
            writebacks,
            payload,
            section_contexts,
            dry_run,
            review_backend=review_backend,
            oracle_timeout=oracle_timeout,
            oracle_model=oracle_model,
            oracle_pdf=oracle_pdf,
        )
        attempts.append({"attempt": attempt, "review": review, "writebacks": writebacks})

        if review.get("gate_passed"):
            accepted_writebacks = writebacks
            accepted_review = review
            accepted_plan = candidate_plan
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
            codex_changes = review.get("codex", {}).get("required_changes", [])
            secondary_key = "oracle" if "oracle" in review else "claude"
            secondary_review = review.get(secondary_key, {})
            secondary_issues = secondary_review.get("issues", [])
            secondary_changes = secondary_review.get("required_changes", [])
            deep_feedback = json.dumps({
                "codex_issues": codex_issues,
                f"{secondary_key}_issues": secondary_issues,
                "codex_required_changes": codex_changes,
                f"{secondary_key}_required_changes": secondary_changes,
                "codex_score": review.get("codex", {}).get("score", 0),
                f"{secondary_key}_score": secondary_review.get("score", 0),
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
                f"{secondary_key}={secondary_review.get('score', 0)}); "
                f"{_compact_review_feedback(review)}"
            )
            save_state(state)
            continue

        feedback = _json_block(review)
        secondary_key = "oracle" if "oracle" in review else "claude"
        secondary_score = review.get(secondary_key, {}).get("score", 0)
        state.prior_feedback.append(
            f"W attempt {attempt}: review gate below {SCORE_PASS_THRESHOLD} "
            f"(codex={review.get('codex', {}).get('score', 0)}, "
            f"{secondary_key}={secondary_score}); "
            f"{_compact_review_feedback(review)}"
        )
        save_state(state)  # persist feedback in case of crash/restart

    if not accepted_writebacks:
        score_key = f"W_cycle{state.depth_cycle}" if state.depth_cycle > 0 else "W"
        last_review = {}
        for attempt_data in reversed(attempts):
            if isinstance(attempt_data, dict) and attempt_data.get("review"):
                last_review = attempt_data["review"]
                break
        if last_review:
            state.scores[score_key] = last_review
        _write_artifact_json(
            state,
            "blocked.json",
            {
                "stage": "W",
                "status": "review_failed",
                "depth_cycle": state.depth_cycle,
                "focused_family": focused_family,
                "attempt_count": len(attempts),
                "last_review": last_review,
                "resume_stage": "W",
                "updated_at": _now_iso(),
            },
        )
        _write_artifact_json(state, "writeback_response.json", {"attempts": attempts})
        save_state(state)
        logger.error("Stage W failed review gate")
        return False

    _write_artifact_json(
        state,
        "writeback_response.json",
        {"attempts": attempts, "accepted_review": accepted_review},
    )

    plan = accepted_plan
    if not plan:
        plan, plan_errors = _plan_writeback_application(accepted_writebacks)
    else:
        plan_errors = []
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
    status = "dry_run" if dry_run else "applied" if applied else "skipped"
    _append_writeback_ledger(
        state,
        status=status,
        focused_family=focused_family,
        accepted_writebacks=accepted_writebacks,
        applied=applied,
        skipped=skipped,
        review=accepted_review,
    )
    state.current_stage = "E"
    score_key = f"W_cycle{state.depth_cycle}" if state.depth_cycle > 0 else "W"
    state.scores[score_key] = accepted_review
    # Mark focused family as completed for deepening tracking
    family_integrated = bool(applied) or dry_run
    if focused_family and family_integrated:
        family_name = focused_family.get("name", "")
        if family_name and family_name not in state.completed_families:
            state.completed_families.append(family_name)
            logger.info("Marked family '%s' complete (total: %d)",
                        family_name, len(state.completed_families))
    elif focused_family:
        logger.warning(
            "Family '%s' not marked complete because no writebacks were applied",
            focused_family.get("name", ""),
        )
    state.round_number += 1
    save_state(state)
    logger.info("Stage W completed for %s (cycle %d)", state.name, state.depth_cycle)
    return True


def _registry_entry(state: DistillState) -> dict[str, Any]:
    """Build the knowledge backflow registry entry for a completed distillation."""
    payload = _read_artifact_json(state, "generated_payload.json")
    writebacks_path = _artifact_path(state, "writebacks.json")
    writebacks = read_json(writebacks_path) if writebacks_path.exists() else {}
    source_slug = _slugify(
        payload.get("knowledge_payload", {}).get("source_slug")
        or _slugify(state.name)
    )
    primary_targets = payload.get("primary_targets") or payload.get(
        "navigation_payload",
        {},
    ).get("target_sections", [])
    integrated = []
    ledger_path = _artifact_path(state, "writeback_ledger.json")
    if ledger_path.exists():
        try:
            ledger = read_json(ledger_path)
        except (OSError, json.JSONDecodeError):
            ledger = []
        if isinstance(ledger, list):
            for entry in ledger:
                if not isinstance(entry, dict):
                    continue
                for item in entry.get("applied", []):
                    integrated.extend(item.get("labels", []))
                if entry.get("status") in ("dry_run", "skipped") and not entry.get("applied"):
                    for item in entry.get("writebacks", []):
                        label = item.get("label")
                        if label:
                            integrated.append(label)
    for item in writebacks.get("applied", []):
        integrated.extend(item.get("labels", []))
    if not integrated:
        for item in writebacks.get("writebacks", []):
            label = item.get("label")
            if label:
                integrated.append(label)
    integrated = list(dict.fromkeys(integrated))
    compact_queue = []
    for item in payload.get("expansion_queue", []):
        if not isinstance(item, dict):
            continue
        target_sections = _unique_strings(item.get("target_sections", []))
        status = str(item.get("status", "active") or "active")
        kernel = str(item.get("kernel", "")).strip()
        digest_source = json.dumps(
            {
                "kernel": kernel,
                "target_sections": target_sections,
                "status": status,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
        compact_queue.append(
            {
                "queue_id": hashlib.sha1(digest_source.encode("utf-8")).hexdigest()[:12],
                "target_sections": target_sections,
                "status": status,
            }
        )
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
        "expansion_queue": compact_queue,
    }


def _merge_unique_sequence(left: Any, right: Any) -> list[Any]:
    """Merge two JSON lists while preserving first-seen order."""
    merged = []
    seen = set()
    for item in (left or []) + (right or []):
        key = json.dumps(item, ensure_ascii=False, sort_keys=True, default=str)
        if key in seen:
            continue
        seen.add(key)
        merged.append(item)
    return merged


def _merge_registry_entries(existing: dict[str, Any], incoming: dict[str, Any]) -> dict[str, Any]:
    """Merge repeated registrations for the same normalized source slug."""
    merged = dict(existing)
    merged["source_slug"] = _slugify(
        incoming.get("source_slug") or existing.get("source_slug") or ""
    )
    original_date = existing.get("date_created")
    if original_date:
        merged["date_created"] = original_date
    elif incoming.get("date_created"):
        merged["date_created"] = incoming["date_created"]

    for key in ("source_type", "integration_mode"):
        left = str(existing.get(key, "")).strip()
        right = str(incoming.get(key, "")).strip()
        if left and right and left != right:
            merged[key] = "+".join(_merge_unique_sequence([left], [right]))
        else:
            merged[key] = right or left

    if existing.get("primary_note") and incoming.get("primary_note"):
        notes = _merge_unique_sequence(
            existing.get("primary_notes") or [existing.get("primary_note")],
            incoming.get("primary_notes") or [incoming.get("primary_note")],
        )
        merged["primary_note"] = notes[0]
        merged["primary_notes"] = notes
    else:
        merged["primary_note"] = incoming.get("primary_note") or existing.get("primary_note", "")

    for key in ("primary_targets", "integrated_writebacks", "expansion_queue"):
        merged[key] = _merge_unique_sequence(existing.get(key, []), incoming.get(key, []))
    return merged


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
    entry = dict(entry)
    entry["source_slug"] = _slugify(entry.get("source_slug", ""))
    registry = _read_registry()
    output = []
    replaced = False
    for existing in registry:
        existing_slug = _slugify(str(existing.get("source_slug", "")))
        existing = dict(existing)
        existing["source_slug"] = existing_slug
        if existing_slug == entry["source_slug"]:
            output.append(_merge_registry_entries(existing, entry))
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
        "| 来源 | 状态 | 目标章节 | 写回数 | 待扩张数 |",
        "|---|---|---|---:|---:|",
    ]
    for entry in sorted(registry, key=lambda item: str(item.get("source_slug", ""))):
        targets = ", ".join(str(item) for item in entry.get("primary_targets", []))
        writeback_count = len(entry.get("integrated_writebacks", []))
        queue_count = len(entry.get("expansion_queue", []))
        lines.append(
            "| `{}` | {} | {} | {} | {} |".format(
                entry.get("source_slug", ""),
                BOARD_STATUS_LABELS.get(str(entry.get("status", "")).strip(), entry.get("status", "")),
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
        text = "# 蒸馏看板\n\n"
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
    """Return the next scoped theorem family to deepen, or None if exhausted."""
    payload: dict[str, Any] = {}
    try:
        payload = _read_artifact_json(state, "generated_payload.json")
    except FileNotFoundError:
        payload = {}
    try:
        raw = _read_artifact_json(state, "raw_research.json")
    except FileNotFoundError:
        raw = {}
    families = _payload_theorem_families(payload) or _raw_theorem_families(raw)
    coverage_targets: dict[str, list[str]] = {}
    for debt in _active_coverage_debts(payload, state.completed_families):
        family_name = str(debt.get("family", "")).strip()
        if family_name and family_name not in coverage_targets:
            coverage_targets[family_name] = _unique_strings(
                debt.get("target_sections", [])
            )
    for family in families:
        name = family.get("name", "")
        if not name or name in state.completed_families:
            continue
        scoped_family = dict(family)
        scoped_targets = _unique_strings(scoped_family.get("target_sections", []))
        debt_targets = coverage_targets.get(str(name).strip(), [])
        if debt_targets:
            # Stage G coverage debts are the current scoped repair contract.
            scoped_targets = debt_targets
        if scoped_targets:
            scoped_family["target_sections"] = scoped_targets
        return scoped_family
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
        str(DISTILLATION_MEMORY_PATH),
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


COMMITTABLE_REGISTRY_FILES = {
    REGISTRY_PATH.resolve(),
    DISTILLATION_MEMORY_PATH.resolve(),
    (PUBLICATION_DIR / "DISTILLATION_BOARD.md").resolve(),
}


def _is_relative_to(path: Path, parent: Path) -> bool:
    """Compatibility wrapper for Path.relative_to checks."""
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def _is_committable_pipeline_output(path: Path) -> bool:
    """Return whether the distillation auto-commit may stage this path.

    Runtime artifacts are intentionally local-only.  The auto-commit allowlist is
    limited to actual paper writebacks and public registry summaries.
    """
    resolved = path.resolve()
    if _is_relative_to(resolved, DISTILLATION_DIR):
        return False
    if resolved in COMMITTABLE_REGISTRY_FILES:
        return True
    if _is_relative_to(resolved, CORE_BODY) and resolved.suffix == ".tex":
        return True
    return False


def _git_stage_files(name: str, stage: str, extra_files: Optional[list[str]] = None) -> None:
    """Stage (git add) outputs for the given stage. Does NOT commit."""
    files_to_add = list(extra_files or [])

    if stage in STAGE_COMMIT_FILES:
        files_to_add.extend(STAGE_COMMIT_FILES[stage])

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
        return

    rejected = []
    filtered = []
    for item in files_to_add:
        path = Path(item)
        if not path.exists():
            continue
        if _is_committable_pipeline_output(path):
            filtered.append(str(path))
        else:
            rejected.append(str(path))
    if rejected:
        logger.info(
            "Stage %s: skipped %d non-committable runtime artifact(s)",
            stage,
            len(rejected),
        )
    if not filtered:
        return

    try:
        subprocess.run(
            ["git", "add"] + filtered,
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=30,
        )
        logger.info("Stage %s: staged %d file(s)", stage, len(filtered))
    except (subprocess.TimeoutExpired, OSError) as exc:
        logger.warning("Stage %s: git add failed: %s", stage, exc)


def _build_commit_summary(name: str) -> str:
    """Build a descriptive commit body from writeback data."""
    lines: list[str] = []
    wb_path = _state_dir(name) / "writebacks.json"
    if wb_path.exists():
        try:
            wb_data = read_json(wb_path)
            applied = wb_data.get("applied", [])
            if applied:
                # Collect sections touched
                sections: set[str] = set()
                total_lines = 0
                for item in applied:
                    tex = item.get("tex_file", "")
                    parts = tex.replace("\\", "/").split("/")
                    if len(parts) >= 2:
                        sections.add(parts[0])
                    total_lines += item.get("line_count", 0)
                n_theorems = sum(len(item.get("labels", [])) for item in applied)
                lines.append(
                    f"{n_theorems} theorem(s) across {len(applied)} file(s), "
                    f"~{total_lines} lines"
                )
                if sections:
                    lines.append(f"sections: {', '.join(sorted(sections))}")
        except (OSError, json.JSONDecodeError, KeyError):
            pass
    return "\n".join(lines)


def _git_commit_batch(name: str, label: str) -> None:
    """Commit all staged files as one batch. Best-effort, never fatal."""
    slug = _slugify(name)
    title = f"distill({slug}): {label}"
    body = _build_commit_summary(name)
    msg = f"{title}\n\n{body}" if body else title
    try:
        diff = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            cwd=str(REPO_ROOT), capture_output=True, timeout=10,
        )
        if diff.returncode == 0:
            logger.info("Batch commit: nothing staged for %s", name)
            return
        subprocess.run(
            ["git", "commit", "-m", msg],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=30,
        )
        subprocess.run(
            ["git", "push"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=60,
        )
        logger.info("Batch commit: committed and pushed for %s", name)
    except (subprocess.TimeoutExpired, OSError) as exc:
        logger.warning("Batch commit failed for %s: %s", name, exc)


def _git_commit_push(name: str, stage: str, extra_files: Optional[list[str]] = None) -> None:
    """Legacy entry point — now delegates to stage + batch commit."""
    _git_stage_files(name, stage, extra_files)
    _git_commit_batch(name, f"stage {stage} ({STAGE_NAMES.get(stage, stage)}) complete")


def run_pipeline(
    name: str,
    skip_to: Optional[str] = None,
    dry_run: bool = False,
    supervised: bool = True,
    review_backend: str = DEFAULT_REVIEW_BACKEND,
    oracle_research: bool = False,
    oracle_deepening: bool = False,
    oracle_timeout: int = DEFAULT_ORACLE_TIMEOUT,
    oracle_model: str = DEFAULT_ORACLE_MODEL,
    oracle_pdf: Optional[Path] = None,
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
    state = reconcile_state_contract(state)

    while state.current_stage != "DONE":
        state = reconcile_state_contract(load_state(name))
        action = refresh_policy_state(state)
        action_kind = str(action.get("action", ""))
        if action_kind == "done":
            if state.current_stage != "DONE":
                state.current_stage = "DONE"
                save_state(state)
            break
        if action_kind == "blocked":
            logger.error(
                "Policy gate blocked %s at %s: %s",
                name,
                action.get("gate"),
                action.get("reason"),
            )
            return False
        stage = str(action.get("stage") or state.current_stage)
        if stage not in STAGE_ORDER[:-1]:
            logger.error("Policy selected invalid stage %s", stage)
            return False
        if state.current_stage != stage:
            logger.info(
                "Policy rerouted %s: %s -> %s (%s)",
                name,
                state.current_stage,
                stage,
                action.get("reason"),
            )
            state.current_stage = stage
            save_state(state)
        if STOP_FILE.exists():
            logger.warning("Stop file present; pausing before stage %s", state.current_stage)
            if not dry_run:
                _git_commit_batch(name, f"partial (stop file before stage {state.current_stage})")
            return False
        logger.info(
            "Policy action for %s: stage=%s gate=%s reason=%s",
            name,
            stage,
            action.get("gate"),
            action.get("reason"),
        )
        if stage == "R":
            ok = run_stage_r(
                state,
                dry_run=dry_run,
                oracle_research=oracle_research,
                oracle_timeout=oracle_timeout,
                oracle_model=oracle_model,
                oracle_pdf=oracle_pdf,
            )
        elif stage == "S":
            ok = run_stage_s(state, dry_run=dry_run)
        elif stage == "G":
            ok = run_stage_g(state, dry_run=dry_run)
        elif stage == "W":
            ok = run_stage_w(
                state,
                dry_run=dry_run,
                supervised=supervised,
                review_backend=review_backend,
                oracle_deepening=oracle_deepening,
                oracle_timeout=oracle_timeout,
                oracle_model=oracle_model,
                oracle_pdf=oracle_pdf,
            )
        elif stage == "E":
            ok = run_stage_e(state, dry_run=dry_run)
        else:
            logger.error("No runner for stage %s", stage)
            return False
        if not ok:
            logger.error("Pipeline stopped at stage %s", stage)
            # Safety net: commit whatever was staged so work isn't lost
            if not dry_run:
                _git_commit_batch(name, f"partial (stopped at stage {stage})")
            return False
        # Stage files for later batch commit (skip in dry-run)
        if not dry_run:
            _git_stage_files(name, stage)
        state = reconcile_state_contract(load_state(name))
        refresh_policy_state(state)
    # Batch commit all accumulated stages at DONE
    if not dry_run:
        _git_commit_batch(name, "complete (all stages)")
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
        state = reconcile_state_contract(load_state(item_name))
        _scope, inventory, action = _policy_model(state)
        done, reason = _pipeline_done_contract(state)
        family_count = len(_theorem_family_names(state))
        debt_count = len(_open_debts_from_inventory(inventory))
        next_action = action.get("stage") if action.get("action") != "blocked" else "BLOCKED"
        lines.append(
            f"{state.name}: stage={state.current_stage} "
            f"round={state.round_number} "
            f"families={len(state.completed_families)}/{family_count} "
            f"debts={debt_count} splits={len(inventory.get('split_candidates', []))} "
            f"next={next_action} gate={action.get('gate')} "
            f"done_contract={done} ({reason}) "
            f"updated={state.updated_at}"
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
        "oracle_research.txt",
        "semantic_scan.txt",
        "generate.txt",
        "writeback.txt",
        "deepen.txt",
        "deep_research_directive.txt",
        "review_codex.txt",
        "review_claude.txt",
        "oracle_deepening.txt",
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
    logger.info("Default review backend: %s", DEFAULT_REVIEW_BACKEND)
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
    parser.add_argument(
        "--review-backend",
        choices=REVIEW_BACKENDS,
        default=DEFAULT_REVIEW_BACKEND,
        help="Review gate backend: codex or codex-claude",
    )
    parser.add_argument(
        "--oracle-research",
        action="store_true",
        help="Use ChatGPT Oracle as the first Stage R deep-research pass",
    )
    parser.add_argument(
        "--oracle-deepening",
        action="store_true",
        help="Use ChatGPT Oracle as a Stage W deep-research expansion layer, not as a reviewer",
    )
    parser.add_argument(
        "--oracle-timeout",
        type=int,
        default=DEFAULT_ORACLE_TIMEOUT,
        help="Seconds to wait for ChatGPT Oracle research",
    )
    parser.add_argument(
        "--oracle-model",
        default=DEFAULT_ORACLE_MODEL,
        help="Model label passed to the ChatGPT Oracle bridge",
    )
    parser.add_argument(
        "--oracle-pdf",
        type=Path,
        help="Optional project PDF to attach to ChatGPT Oracle research",
    )
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
                review_backend=args.review_backend,
                oracle_research=args.oracle_research,
                oracle_deepening=args.oracle_deepening,
                oracle_timeout=args.oracle_timeout,
                oracle_model=args.oracle_model,
                oracle_pdf=args.oracle_pdf,
            ) and all_ok
        if not args.continuous or STOP_FILE.exists():
            return 0 if all_ok else 1
        logger.info("Continuous mode sleeping for 20s")
        time.sleep(20)


if __name__ == "__main__":
    sys.exit(main())
