#!/usr/bin/env python3
"""Omega Autoresearch — overnight autonomous Lean4 formalization loop.

Adapts Karpathy's autoresearch pattern for Lean4 theorem proving:
  - Read target from manifest (LaTeX theorem)
  - Call LLM to generate complete Lean4 code (statement + proof)
  - Compile with lake build
  - Pass → git commit on scratch branch, cherry-pick to dev
  - Fail → repair cycle (max 3 rounds), then revert

Usage:
    python run_overnight.py --budget 20 --model claude-sonnet
    python run_overnight.py --budget 200 --model claude-sonnet --max-cost 50
    python run_overnight.py --targets manifest.jsonl --budget 5 --dry-run
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
LEAN_ROOT = REPO_ROOT / "lean4"
OMEGA_ROOT = LEAN_ROOT / "Omega"
PROGRAM_MD = SCRIPT_DIR / "program.md"
TRACES_DIR = SCRIPT_DIR / "traces"
LOCK_FILE = SCRIPT_DIR / ".run_overnight.lock"

sys.path.insert(0, str(LEAN_ROOT / "scripts"))
import omega_ci  # noqa: E402

NYXID_DIR = Path.home() / ".nyxid"
NYXID_SERVICE_SLUG = "aelf-llm-at3l"

FORBIDDEN_TOKENS = {"sorry", "admit", "axiom"}
FORBIDDEN_RE = omega_ci.re.compile(r"\b(?:sorry|admit|axiom)\b")
MAX_FILE_LINES = 800
BUILD_TIMEOUT = 300  # seconds
MAX_REPAIR_ROUNDS = 3
CIRCUIT_BREAKER_THRESHOLD = 10
CIRCUIT_BREAKER_PAUSE = 1800  # 30 minutes

# Cost estimates ($/1M tokens) — update as pricing changes
MODEL_COSTS = {
    "claude-sonnet": {"input": 3.0, "output": 15.0},
    "claude-haiku": {"input": 0.25, "output": 1.25},
    "claude-opus": {"input": 15.0, "output": 75.0},
}


def utcnow_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def acquire_lock() -> int:
    """Acquire PID lock. Returns fd on success, raises on failure."""
    LOCK_FILE.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(str(LOCK_FILE), os.O_CREAT | os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        os.close(fd)
        raise RuntimeError(
            f"Another run_overnight instance is running (lock: {LOCK_FILE})"
        )
    os.write(fd, str(os.getpid()).encode())
    os.fsync(fd)
    return fd


def release_lock(fd: int) -> None:
    fcntl.flock(fd, fcntl.LOCK_UN)
    os.close(fd)
    LOCK_FILE.unlink(missing_ok=True)


def load_manifest(path: Path) -> list[dict]:
    targets = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                targets.append(json.loads(line))
    return targets


def load_program_md() -> str:
    return PROGRAM_MD.read_text(encoding="utf-8")


def load_nyxid_credentials(base_url_override: str | None) -> tuple[str, str | None]:
    """Read NyxID access token from ~/.nyxid/ and construct proxy URL.

    Returns (token, base_url). Token is empty string if not available.
    """
    token_file = NYXID_DIR / "access_token"
    base_url_file = NYXID_DIR / "base_url"
    if not token_file.exists():
        return "", base_url_override
    token = token_file.read_text().strip()
    if not token:
        return "", base_url_override
    if not base_url_override:
        nyx_base = "https://nyx-api.chrono-ai.fun"
        if base_url_file.exists():
            nyx_base = base_url_file.read_text().strip()
        base_url_override = f"{nyx_base}/api/v1/proxy/s/{NYXID_SERVICE_SLUG}/v1"
    return token, base_url_override


def call_llm_anthropic(
    prompt: str,
    model_id: str,
    max_tokens: int,
    api_key: str,
) -> tuple[str, dict]:
    """Call Anthropic API."""
    try:
        import anthropic
        client = anthropic.Anthropic(api_key=api_key)
        message = client.messages.create(
            model=model_id,
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}],
        )
        text = message.content[0].text if message.content else ""
        usage = {
            "input_tokens": message.usage.input_tokens,
            "output_tokens": message.usage.output_tokens,
        }
        return text, usage
    except ImportError:
        pass

    # Fallback: curl
    import tempfile
    payload = {
        "model": model_id,
        "max_tokens": max_tokens,
        "messages": [{"role": "user", "content": prompt}],
    }
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
        json.dump(payload, f)
        tmp_path = f.name
    try:
        result = subprocess.run(
            [
                "curl", "-s", "https://api.anthropic.com/v1/messages",
                "-H", f"x-api-key: {api_key}",
                "-H", "anthropic-version: 2023-06-01",
                "-H", "content-type: application/json",
                "-d", f"@{tmp_path}",
            ],
            capture_output=True, text=True, timeout=120,
        )
        data = json.loads(result.stdout)
        text = data.get("content", [{}])[0].get("text", "")
        usage = data.get("usage", {})
        return text, {
            "input_tokens": usage.get("input_tokens", 0),
            "output_tokens": usage.get("output_tokens", 0),
        }
    finally:
        os.unlink(tmp_path)


def call_llm_codex(prompt: str, repo_root: str) -> tuple[str, dict]:
    """Call Codex CLI as the LLM backend."""
    import tempfile
    prompt_file = tempfile.mktemp(suffix=".txt")
    with open(prompt_file, "w") as f:
        f.write(prompt)
    try:
        result = subprocess.run(
            [
                "codex", "exec", f"$(cat {prompt_file})",
                "-C", repo_root,
                "-s", "read-only",
            ],
            capture_output=True, text=True, timeout=300,
        )
        text = result.stdout.strip()
        usage = {"input_tokens": 0, "output_tokens": 0}  # Codex doesn't report tokens
        return text, usage
    except subprocess.TimeoutExpired:
        return "", {"input_tokens": 0, "output_tokens": 0}
    finally:
        os.unlink(prompt_file)


def call_llm_openai(
    prompt: str,
    model_id: str,
    max_tokens: int,
    api_key: str,
    base_url: str | None = None,
) -> tuple[str, dict]:
    """Call OpenAI-compatible API via openai SDK."""
    import openai
    # Custom User-Agent avoids WAF blocks on some OpenAI-compatible gateways
    # See: https://github.com/ChronoAIProject/NyxID/issues/184
    kwargs = {"api_key": api_key, "default_headers": {"User-Agent": "omega-autoresearch/1.0"}}
    if base_url:
        kwargs["base_url"] = base_url
    client = openai.OpenAI(**kwargs)

    # Try chat/completions first
    try:
        response = client.chat.completions.create(
            model=model_id,
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}],
        )
        text = response.choices[0].message.content or ""
        usage = {
            "input_tokens": response.usage.prompt_tokens if response.usage else 0,
            "output_tokens": response.usage.completion_tokens if response.usage else 0,
        }
        return text, usage
    except Exception as chat_err:
        # Fallback: try responses API
        try:
            response = client.responses.create(
                model=model_id,
                input=prompt,
            )
            # Extract text from responses format
            text = ""
            if hasattr(response, "output"):
                for item in response.output:
                    if hasattr(item, "content"):
                        for c in item.content:
                            if hasattr(c, "text"):
                                text += c.text
                    elif hasattr(item, "text"):
                        text += item.text
            usage = {
                "input_tokens": getattr(response.usage, "input_tokens", 0) if hasattr(response, "usage") else 0,
                "output_tokens": getattr(response.usage, "output_tokens", 0) if hasattr(response, "usage") else 0,
            }
            return text, usage
        except Exception:
            raise chat_err  # Re-raise original error if both fail


def call_llm(
    prompt: str,
    model: str = "claude-sonnet",
    max_tokens: int = 4096,
    *,
    api_key: str | None = None,
) -> tuple[str, dict]:
    """Route to the appropriate LLM backend based on model name."""
    ANTHROPIC_MODELS = {
        "claude-sonnet": "claude-sonnet-4-20250514",
        "claude-haiku": "claude-haiku-4-5-20251001",
        "claude-opus": "claude-opus-4-20250514",
    }
    OPENAI_MODELS = {
        "gpt-4o": "gpt-4o",
        "gpt-4o-mini": "gpt-4o-mini",
        "o3": "o3",
        "o4-mini": "o4-mini",
    }

    if model == "codex":
        return call_llm_codex(prompt, str(REPO_ROOT))

    if model in OPENAI_MODELS or model.startswith("gpt-") or model.startswith("o"):
        key = api_key or os.environ.get("OPENAI_API_KEY", "")
        base_url = os.environ.get("OPENAI_BASE_URL", None)

        # NyxID fallback: read access_token from ~/.nyxid/
        if not key:
            key, base_url = load_nyxid_credentials(base_url)

        if not key:
            raise RuntimeError(
                "OPENAI_API_KEY not set. Set env var, pass --api-key, "
                "or login via: nyxid login"
            )
        model_id = OPENAI_MODELS.get(model, model)
        return call_llm_openai(prompt, model_id, max_tokens, key, base_url)

    # Default: Anthropic
    key = api_key or os.environ.get("ANTHROPIC_API_KEY", "")
    if not key:
        raise RuntimeError(
            "ANTHROPIC_API_KEY not set. Export it or pass --api-key."
        )
    model_id = ANTHROPIC_MODELS.get(model, model)
    return call_llm_anthropic(prompt, model_id, max_tokens, key)


def extract_lean_code(response: str) -> str:
    """Extract Lean4 code from LLM response (strip markdown fences)."""
    lines = response.split("\n")
    in_block = False
    code_lines = []
    for line in lines:
        if line.strip().startswith("```lean") or line.strip().startswith("```lean4"):
            in_block = True
            continue
        if line.strip() == "```" and in_block:
            in_block = False
            continue
        if in_block:
            code_lines.append(line)

    if code_lines:
        return "\n".join(code_lines).strip()
    # No fences found — treat entire response as code if it looks like Lean
    stripped = response.strip()
    if any(kw in stripped for kw in ("theorem ", "lemma ", "def ", "instance ")):
        return stripped
    return ""


def check_forbidden_tokens(code: str) -> list[str]:
    """Check for sorry/admit/axiom in generated code."""
    violations = []
    for i, line in enumerate(code.split("\n"), 1):
        # Skip comments
        stripped = line.split("--")[0]
        for token in FORBIDDEN_TOKENS:
            if omega_ci.re.search(rf"\b{token}\b", stripped):
                violations.append(f"line {i}: forbidden token '{token}'")
    return violations


def check_file_size(filepath: Path, new_code: str) -> bool:
    """Check if appending code would exceed MAX_FILE_LINES."""
    existing = filepath.read_text().count("\n") if filepath.exists() else 0
    new_lines = new_code.count("\n") + 1
    return (existing + new_lines) <= MAX_FILE_LINES


def find_target_file(target: dict) -> Path:
    """Determine which .lean file to append to (or create)."""
    module = target.get("target_module", "Omega/Frontier")
    module_dir = LEAN_ROOT / module

    if not module_dir.exists():
        module_dir = LEAN_ROOT / "Omega" / "Frontier"

    # Find existing files in the module directory
    lean_files = sorted(module_dir.glob("*.lean"))

    if lean_files:
        # Pick the file with the most related content (by label prefix)
        label = target.get("label", "")
        best_file = lean_files[0]
        best_score = -1
        for f in lean_files:
            text = f.read_text(encoding="utf-8")
            # Simple heuristic: count how many similar labels are in this file
            label_parts = label.split(":")[-1].split("-") if ":" in label else []
            score = sum(1 for part in label_parts if part in text.lower())
            if score > best_score:
                best_score = score
                best_file = f
        return best_file

    # No files in module — will need to create one
    label = target.get("label", "unknown")
    slug = label.split(":")[-1].replace("-", "_").replace(".", "_")[:40]
    return module_dir / f"{slug}.lean"


def apply_code_to_file(filepath: Path, code: str, target: dict) -> bool:
    """Append generated code to the target file. Returns True if file was created."""
    created = not filepath.exists()

    if created:
        filepath.parent.mkdir(parents=True, exist_ok=True)
        filepath.write_text(code + "\n", encoding="utf-8")
    else:
        with open(filepath, "a", encoding="utf-8") as f:
            f.write("\n\n" + code + "\n")

    return created


def update_omega_imports(new_file: Path) -> None:
    """Add import for a new .lean file to Omega.lean."""
    omega_lean = LEAN_ROOT / "Omega.lean"
    if not omega_lean.exists():
        return

    rel = new_file.relative_to(LEAN_ROOT).with_suffix("")
    module_name = ".".join(rel.parts)
    import_line = f"import {module_name}"

    text = omega_lean.read_text(encoding="utf-8")
    if import_line in text:
        return

    # Find the right insertion point (after last import in same module group)
    lines = text.split("\n")
    module_prefix = ".".join(rel.parts[:2])  # e.g., "Omega.Folding"
    insert_idx = len(lines)

    for i, line in enumerate(lines):
        if line.startswith(f"import {module_prefix}"):
            insert_idx = i + 1

    if insert_idx == len(lines):
        # No matching group found — append before the first blank line after imports
        for i, line in enumerate(lines):
            if line.startswith("import "):
                insert_idx = i + 1

    lines.insert(insert_idx, import_line)
    omega_lean.write_text("\n".join(lines), encoding="utf-8")


def run_build(filepath: Path | None = None) -> tuple[bool, str]:
    """Run lake build. Returns (success, error_output)."""
    cmd = ["timeout", str(BUILD_TIMEOUT), "lake", "build"]
    try:
        result = subprocess.run(
            cmd, cwd=str(LEAN_ROOT),
            capture_output=True, text=True,
            timeout=BUILD_TIMEOUT + 30,
        )
        stderr = result.stderr or ""
        stdout = result.stdout or ""
        output = stdout + stderr
        success = result.returncode == 0 and "error:" not in output.lower()
        return success, output
    except subprocess.TimeoutExpired:
        return False, "BUILD TIMEOUT"
    except Exception as e:
        return False, f"BUILD EXCEPTION: {e}"


def git_current_branch() -> str:
    """Get the current git branch name."""
    result = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=str(REPO_ROOT), capture_output=True, text=True,
    )
    return result.stdout.strip() or "dev"


def git_setup_scratch_branch() -> tuple[str, str]:
    """Create and checkout a scratch branch. Returns (scratch_branch, base_branch)."""
    base_branch = git_current_branch()
    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    scratch_name = f"autoresearch-{ts}"
    subprocess.run(
        ["git", "checkout", "-b", scratch_name],
        cwd=str(REPO_ROOT), capture_output=True, check=True,
    )
    return scratch_name, base_branch


def git_commit(filepath: Path, target: dict, created_new_file: bool) -> None:
    """Commit the current change."""
    files_to_add = [str(filepath.relative_to(REPO_ROOT))]
    if created_new_file:
        omega_lean = LEAN_ROOT / "Omega.lean"
        files_to_add.append(str(omega_lean.relative_to(REPO_ROOT)))

    for f in files_to_add:
        subprocess.run(
            ["git", "add", f], cwd=str(REPO_ROOT),
            capture_output=True, check=True,
        )

    label = target.get("label", "unknown")
    msg = f"autoresearch: formalize {label}"
    subprocess.run(
        ["git", "commit", "-m", msg],
        cwd=str(REPO_ROOT), capture_output=True, check=True,
    )


def git_revert_changes() -> None:
    """Revert all uncommitted changes including untracked files."""
    subprocess.run(
        ["git", "checkout", "--", "."],
        cwd=str(REPO_ROOT), capture_output=True,
    )
    subprocess.run(
        ["git", "clean", "-fd", "--", "lean4/Omega/"],
        cwd=str(REPO_ROOT), capture_output=True,
    )


def git_cherry_pick_to_base(scratch_branch: str, base_branch: str) -> list[str]:
    """Cherry-pick all commits from scratch branch to the base branch."""
    result = subprocess.run(
        ["git", "log", "--oneline", f"{base_branch}..{scratch_branch}"],
        cwd=str(REPO_ROOT), capture_output=True, text=True,
    )
    commits = [line.split()[0] for line in result.stdout.strip().split("\n") if line.strip()]
    if not commits:
        return []

    subprocess.run(
        ["git", "checkout", base_branch],
        cwd=str(REPO_ROOT), capture_output=True, check=True,
    )

    picked = []
    for commit_hash in reversed(commits):
        cp_result = subprocess.run(
            ["git", "cherry-pick", commit_hash],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
        )
        if cp_result.returncode == 0:
            picked.append(commit_hash)
        else:
            # Abort failed cherry-pick
            subprocess.run(
                ["git", "cherry-pick", "--abort"],
                cwd=str(REPO_ROOT), capture_output=True,
            )
            break

    return picked


def log_trace(trace: dict) -> None:
    """Append a trace entry to the JSONL log."""
    TRACES_DIR.mkdir(parents=True, exist_ok=True)
    date_str = datetime.now().strftime("%Y%m%d")
    log_file = TRACES_DIR / f"run-{date_str}.jsonl"
    with open(log_file, "a") as f:
        f.write(json.dumps(trace, ensure_ascii=False) + "\n")


def estimate_cost(usage: dict, model: str) -> float:
    """Estimate cost in USD from token usage."""
    costs = MODEL_COSTS.get(model, MODEL_COSTS["claude-sonnet"])
    input_cost = (usage.get("input_tokens", 0) / 1_000_000) * costs["input"]
    output_cost = (usage.get("output_tokens", 0) / 1_000_000) * costs["output"]
    return input_cost + output_cost


def build_prompt(target: dict, program_md: str, context: str = "") -> str:
    """Construct the LLM prompt for a target."""
    label = target.get("label", "")
    body = target.get("body", "")
    tex_file = target.get("tex_file", "")
    tex_line = target.get("tex_line", 0)
    target_module = target.get("target_module", "")

    prompt = f"""{program_md}

## Current Target

Label: {label}
Source: {tex_file}:{tex_line}
Target module: {target_module}

### LaTeX theorem body:
{body}

"""
    if context:
        prompt += f"""### Existing code in target module (for style reference):
{context}

"""
    prompt += """Now generate the Lean4 formalization. Return ONLY the code block."""
    return prompt


def build_repair_prompt(
    target: dict, code: str, error: str, program_md: str
) -> str:
    """Construct the repair prompt with compiler error feedback."""
    label = target.get("label", "")
    return f"""{program_md}

## Repair Task

The previous attempt to formalize {label} produced compiler errors.

### Your previous code:
```lean4
{code}
```

### Compiler errors:
{error}

Fix the code to resolve these errors. Change as little as possible.
Return ONLY the corrected code block.
"""


def gather_context(target: dict) -> str:
    """Gather existing code context from the target module."""
    target_file = find_target_file(target)
    if target_file.exists():
        text = target_file.read_text(encoding="utf-8")
        # Return last 100 lines for style reference
        lines = text.split("\n")
        if len(lines) > 100:
            return "\n".join(lines[-100:])
        return text
    return ""


def run_loop(args: argparse.Namespace) -> int:
    """Main overnight loop."""
    manifest_path = Path(args.targets)
    if not manifest_path.exists():
        print(f"[autoresearch] ERROR: manifest not found: {manifest_path}")
        return 1

    targets = load_manifest(manifest_path)
    if not targets:
        print("[autoresearch] No targets in manifest.")
        return 0

    program_md = load_program_md()

    print(f"[autoresearch] Starting run")
    print(f"  Model: {args.model}")
    print(f"  Budget: {args.budget} targets")
    print(f"  Max cost: ${args.max_cost}")
    print(f"  Targets available: {len(targets)}")
    print(f"  Dry run: {args.dry_run}")
    print()

    # Setup scratch branch
    scratch_branch = None
    base_branch = None
    if not args.dry_run:
        scratch_branch, base_branch = git_setup_scratch_branch()
        print(f"[autoresearch] Base branch: {base_branch}")
        print(f"[autoresearch] Scratch branch: {scratch_branch}")

    # Stats
    attempted = 0
    succeeded = 0
    failed = 0
    errors = 0
    total_cost = 0.0
    consecutive_failures = 0
    start_time = time.time()

    for target in targets:
        if attempted >= args.budget:
            print(f"\n[autoresearch] Budget exhausted ({args.budget} targets)")
            break

        if total_cost >= args.max_cost:
            print(f"\n[autoresearch] Cost limit reached (${total_cost:.2f} >= ${args.max_cost})")
            break

        # Circuit breaker
        if consecutive_failures >= CIRCUIT_BREAKER_THRESHOLD:
            print(f"\n[autoresearch] Circuit breaker: {consecutive_failures} consecutive failures")
            print(f"  Pausing for {CIRCUIT_BREAKER_PAUSE // 60} minutes...")
            if not args.dry_run:
                time.sleep(CIRCUIT_BREAKER_PAUSE)
            consecutive_failures = 0

        label = target.get("label", "unknown")
        priority = target.get("priority", 3)
        attempted += 1

        print(f"\n[{attempted}/{args.budget}] {label} (P{priority})")

        if args.dry_run:
            print(f"  [DRY RUN] Would attempt formalization")
            continue

        # Gather context
        context = gather_context(target)
        target_file = find_target_file(target)

        # Build prompt and call LLM
        prompt = build_prompt(target, program_md, context)
        trace = {
            "ts": utcnow_iso(),
            "label": label,
            "priority": priority,
            "target_file": str(target_file.relative_to(REPO_ROOT)),
            "attempts": [],
            "outcome": "pending",
        }

        success = False
        code = ""
        build_error = ""
        total_attempts_usage = {"input_tokens": 0, "output_tokens": 0}

        for attempt in range(1 + MAX_REPAIR_ROUNDS):
            attempt_label = "initial" if attempt == 0 else f"repair-{attempt}"
            print(f"  [{attempt_label}] Calling LLM...", end=" ", flush=True)

            try:
                if attempt == 0:
                    response, usage = call_llm(prompt, model=args.model, api_key=args.api_key)
                else:
                    repair_prompt = build_repair_prompt(target, code, build_error, program_md)
                    response, usage = call_llm(repair_prompt, model=args.model, api_key=args.api_key)
            except RuntimeError as e:
                if "ANTHROPIC_API_KEY" in str(e):
                    print(f"\n[autoresearch] FATAL: {e}")
                    return 1
                print(f"API error: {e}")
                trace["attempts"].append({"attempt": attempt_label, "error": str(e)})
                errors += 1
                break
            except Exception as e:
                print(f"API error: {e}")
                trace["attempts"].append({"attempt": attempt_label, "error": str(e)})
                errors += 1
                # Exponential backoff
                wait = min(2 ** attempt * 2, 60)
                time.sleep(wait)
                continue

            total_attempts_usage["input_tokens"] += usage.get("input_tokens", 0)
            total_attempts_usage["output_tokens"] += usage.get("output_tokens", 0)

            code = extract_lean_code(response)
            if not code:
                print("empty response")
                trace["attempts"].append({"attempt": attempt_label, "error": "empty_response"})
                continue

            # Check forbidden tokens
            violations = check_forbidden_tokens(code)
            if violations:
                print(f"forbidden tokens: {violations}")
                trace["attempts"].append({
                    "attempt": attempt_label,
                    "error": "forbidden_tokens",
                    "details": violations,
                })
                # Treat as build failure, enter repair with synthetic error
                build_error = "FORBIDDEN: " + "; ".join(violations)
                continue

            # Check file size
            if not check_file_size(target_file, code):
                print(f"file would exceed {MAX_FILE_LINES} lines")
                trace["attempts"].append({
                    "attempt": attempt_label,
                    "error": "file_too_large",
                })
                break  # Can't fix by repair

            # Apply code
            created_new = apply_code_to_file(target_file, code, target)
            if created_new:
                update_omega_imports(target_file)

            # Build
            print("building...", end=" ", flush=True)
            build_ok, build_output = run_build(target_file)

            if build_ok:
                print("PASS")
                git_commit(target_file, target, created_new)
                success = True
                trace["attempts"].append({
                    "attempt": attempt_label,
                    "result": "pass",
                })
                break
            else:
                # Extract error for repair
                build_error = build_output[:3000]  # Limit error size
                error_type = "timeout" if "TIMEOUT" in build_error else "compile_error"
                print(f"FAIL ({error_type})")
                trace["attempts"].append({
                    "attempt": attempt_label,
                    "result": "fail",
                    "error_type": error_type,
                    "error_preview": build_error[:500],
                })
                # Revert before repair attempt
                git_revert_changes()

        if success:
            succeeded += 1
            consecutive_failures = 0
            trace["outcome"] = "success"
        else:
            failed += 1
            consecutive_failures += 1
            trace["outcome"] = "failure"
            git_revert_changes()

        cost = estimate_cost(total_attempts_usage, args.model)
        total_cost += cost
        trace["cost_usd"] = round(cost, 4)
        trace["usage"] = total_attempts_usage
        log_trace(trace)

    # Summary
    elapsed = time.time() - start_time
    elapsed_str = f"{elapsed / 3600:.1f}h" if elapsed > 3600 else f"{elapsed / 60:.1f}m"

    print("\n" + "=" * 60)
    print(f"  AUTORESEARCH RUN SUMMARY")
    print(f"  {'=' * 56}")
    print(f"  Duration:    {elapsed_str}")
    print(f"  Attempted:   {attempted}")
    print(f"  Succeeded:   {succeeded}")
    print(f"  Failed:      {failed}")
    print(f"  Errors:      {errors}")
    print(f"  Cost:        ${total_cost:.2f}")
    if attempted > 0:
        print(f"  Success rate: {succeeded / attempted:.1%}")
    print(f"  {'=' * 56}")

    # Cherry-pick successes to base branch and clean up
    if scratch_branch and base_branch and not args.dry_run:
        if succeeded > 0:
            print(f"\n[autoresearch] Cherry-picking {succeeded} commits to {base_branch}...")
            picked = git_cherry_pick_to_base(scratch_branch, base_branch)
            print(f"  Cherry-picked: {len(picked)}/{succeeded}")
            if len(picked) < succeeded:
                print(f"  WARNING: {succeeded - len(picked)} commits failed to cherry-pick")
        else:
            # No successes — just go back to base branch
            subprocess.run(
                ["git", "checkout", base_branch],
                cwd=str(REPO_ROOT), capture_output=True,
            )

        # Always delete the scratch branch after cherry-pick (or if no successes)
        subprocess.run(
            ["git", "branch", "-D", scratch_branch],
            cwd=str(REPO_ROOT), capture_output=True,
        )
        print(f"  Cleaned up scratch branch: {scratch_branch}")

        # Clean up old autoresearch-* branches (keep none — all work is cherry-picked)
        cleanup = subprocess.run(
            ["git", "branch", "--list", "autoresearch-*"],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
        )
        old_branches = [b.strip() for b in cleanup.stdout.strip().split("\n") if b.strip()]
        for branch in old_branches:
            subprocess.run(
                ["git", "branch", "-D", branch],
                cwd=str(REPO_ROOT), capture_output=True,
            )
        if old_branches:
            print(f"  Cleaned up {len(old_branches)} old autoresearch branch(es)")

    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Omega Autoresearch overnight formalization loop",
    )
    parser.add_argument(
        "--targets",
        default=str(SCRIPT_DIR / "manifest.jsonl"),
        help="Path to target manifest JSONL",
    )
    parser.add_argument(
        "--budget",
        type=int,
        default=20,
        help="Maximum number of targets to attempt (default: 20)",
    )
    parser.add_argument(
        "--model",
        default="claude-sonnet",
        help="LLM model: claude-sonnet|claude-haiku|claude-opus|gpt-4o|o3|codex (default: claude-sonnet)",
    )
    parser.add_argument(
        "--max-cost",
        type=float,
        default=50.0,
        help="Maximum cost in USD (default: 50)",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        help="Anthropic API key (default: ANTHROPIC_API_KEY env var)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be done without actually doing it",
    )
    args = parser.parse_args()

    # Acquire PID lock
    lock_fd = None
    if not args.dry_run:
        try:
            lock_fd = acquire_lock()
        except RuntimeError as e:
            print(f"[autoresearch] {e}")
            return 1

    try:
        return run_loop(args)
    except KeyboardInterrupt:
        print("\n[autoresearch] Interrupted by user")
        git_revert_changes()
        return 130
    finally:
        if lock_fd is not None:
            release_lock(lock_fd)


if __name__ == "__main__":
    raise SystemExit(main())
