#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ChatGPT Pro web oracle — submit prompts and collect responses via browser automation.

Usage:
    # First run: will open browser for manual login, then stays logged in
    python chatgpt_oracle.py --prompt-file prompts/p2_filled.md --output oracle/p2_result.md

    # With model selection (default: o3-mini-high for reasoning)
    python chatgpt_oracle.py --prompt-file input.md --output output.md --model o3-mini-high

    # Quick one-liner prompt
    python chatgpt_oracle.py --prompt "Prove that sqrt(2) is irrational" --output proof.md

    # Interactive mode: just open ChatGPT logged in
    python chatgpt_oracle.py --interactive

Architecture:
    Uses Playwright with persistent browser profile so login persists across runs.
    Browser data stored in ~/.chatgpt_oracle/ (cookies, localStorage).
    No API key needed — uses the free web interface.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from datetime import datetime

# Browser profile directory
PROFILE_DIR = Path.home() / ".chatgpt_oracle"
CHATGPT_URL = "https://chatgpt.com"
DEFAULT_MODEL = "o3-mini-high"

# Timeouts
LOGIN_TIMEOUT_MS = 300_000   # 5 min for manual login
RESPONSE_TIMEOUT_MS = 600_000  # 10 min for long reasoning responses
POLL_INTERVAL_MS = 2_000     # Check every 2s if response is done


def ensure_profile_dir():
    PROFILE_DIR.mkdir(parents=True, exist_ok=True)
    return str(PROFILE_DIR)


def launch_browser(headless: bool = False):
    """Launch persistent browser context."""
    from playwright.sync_api import sync_playwright

    pw = sync_playwright().start()
    browser = pw.chromium.launch_persistent_context(
        user_data_dir=ensure_profile_dir(),
        headless=headless,
        viewport={"width": 1280, "height": 900},
        args=["--disable-blink-features=AutomationControlled"],
    )
    return pw, browser


def wait_for_login(page, timeout_ms: int = LOGIN_TIMEOUT_MS):
    """Wait until user is logged into ChatGPT."""
    print("[oracle] Checking login status...")

    # Navigate to ChatGPT
    page.goto(CHATGPT_URL, wait_until="domcontentloaded", timeout=30_000)
    time.sleep(3)

    # Check if we're on the chat page (logged in) or login page
    # The chat input area indicates we're logged in
    try:
        page.wait_for_selector(
            "#prompt-textarea, div[contenteditable='true'][id='prompt-textarea']",
            timeout=10_000,
        )
        print("[oracle] Already logged in.")
        return True
    except Exception:
        pass

    # Not logged in — ask user to log in manually
    print("[oracle] Not logged in. Please log in manually in the browser window.")
    print(f"[oracle] Waiting up to {timeout_ms // 1000}s for login...")

    try:
        page.wait_for_selector(
            "#prompt-textarea, div[contenteditable='true'][id='prompt-textarea']",
            timeout=timeout_ms,
        )
        print("[oracle] Login successful!")
        return True
    except Exception:
        print("[oracle] ERROR: Login timed out.", file=sys.stderr)
        return False


def select_model(page, model: str):
    """Attempt to select a specific model from the model picker."""
    # This is best-effort — the UI changes frequently
    try:
        # Look for model selector button
        selector_btn = page.query_selector(
            "button[data-testid='model-switcher-dropdown-button'], "
            "button[aria-haspopup='menu'][class*='model']"
        )
        if selector_btn:
            selector_btn.click()
            time.sleep(1)
            # Look for the model option
            model_option = page.query_selector(f"[data-testid*='{model}'], [class*='model-option']:has-text('{model}')")
            if model_option:
                model_option.click()
                time.sleep(0.5)
                print(f"[oracle] Selected model: {model}")
                return True
            else:
                # Close dropdown
                page.keyboard.press("Escape")
                print(f"[oracle] Model '{model}' not found in picker, using default.")
                return False
        else:
            print(f"[oracle] No model selector found, using default.")
            return False
    except Exception as e:
        print(f"[oracle] Model selection failed: {e}")
        return False


def start_new_chat(page):
    """Navigate to a new chat."""
    page.goto(CHATGPT_URL, wait_until="domcontentloaded", timeout=30_000)
    time.sleep(2)
    print("[oracle] New chat ready.")


def submit_prompt(page, prompt: str):
    """Type prompt and send."""
    # Find the textarea
    textarea = page.wait_for_selector(
        "#prompt-textarea",
        timeout=10_000,
    )

    # For long prompts, use clipboard paste (faster and more reliable)
    page.evaluate("""(text) => {
        const el = document.querySelector('#prompt-textarea');
        if (el) {
            // Use the ProseMirror/contenteditable approach
            el.focus();
            // Try setting innerHTML for contenteditable
            if (el.contentEditable === 'true') {
                el.innerHTML = '<p>' + text.replace(/\\n/g, '</p><p>') + '</p>';
                el.dispatchEvent(new Event('input', { bubbles: true }));
            } else {
                // Regular textarea
                el.value = text;
                el.dispatchEvent(new Event('input', { bubbles: true }));
            }
        }
    }""", prompt)

    time.sleep(1)

    # Click send button
    send_btn = page.query_selector(
        "button[data-testid='send-button'], "
        "button[aria-label='Send prompt'], "
        "button[class*='send']"
    )
    if send_btn and send_btn.is_enabled():
        send_btn.click()
        print("[oracle] Prompt submitted.")
    else:
        # Try pressing Enter as fallback
        textarea.press("Enter")
        print("[oracle] Prompt submitted (Enter key).")

    time.sleep(2)


def wait_for_response(page, timeout_ms: int = RESPONSE_TIMEOUT_MS) -> str:
    """Wait for ChatGPT to finish responding, then extract the response text."""
    print("[oracle] Waiting for response...")

    start = time.time()
    max_wait = timeout_ms / 1000

    last_text = ""
    stable_count = 0
    required_stable = 3  # Need 3 consecutive checks with same text

    while time.time() - start < max_wait:
        time.sleep(POLL_INTERVAL_MS / 1000)

        # Check if still generating (look for stop button or streaming indicator)
        is_generating = page.query_selector(
            "button[data-testid='stop-button'], "
            "button[aria-label='Stop generating'], "
            "[class*='result-streaming']"
        )

        if is_generating:
            elapsed = int(time.time() - start)
            if elapsed % 20 == 0 and elapsed > 0:
                print(f"[oracle] Still generating... ({elapsed}s)")
            stable_count = 0
            continue

        # No streaming indicator — check if text is stable
        current_text = extract_response_text(page)
        if current_text and current_text == last_text:
            stable_count += 1
            if stable_count >= required_stable:
                elapsed = int(time.time() - start)
                print(f"[oracle] Response complete ({elapsed}s, {len(current_text)} chars)")
                return current_text
        else:
            stable_count = 0
            last_text = current_text

    print("[oracle] WARNING: Response timeout reached.", file=sys.stderr)
    return extract_response_text(page)


def extract_response_text(page) -> str:
    """Extract the last assistant response from the page."""
    # ChatGPT renders responses in markdown containers
    # Get all assistant message containers
    text = page.evaluate("""() => {
        // Try multiple selectors for response content
        const selectors = [
            '[data-message-author-role="assistant"] .markdown',
            '[data-message-author-role="assistant"]',
            '.agent-turn .markdown',
            '.group\\/conversation-turn .markdown',
        ];

        let elements = [];
        for (const sel of selectors) {
            elements = document.querySelectorAll(sel);
            if (elements.length > 0) break;
        }

        if (elements.length === 0) return '';

        // Get the LAST response (most recent)
        const last = elements[elements.length - 1];
        return last.innerText || last.textContent || '';
    }""")

    return text.strip()


def run_oracle(prompt: str, output_path: str | None, model: str, headless: bool = False) -> str:
    """Full oracle cycle: login -> new chat -> submit -> wait -> extract -> save."""
    pw, browser = launch_browser(headless=headless)

    try:
        page = browser.pages[0] if browser.pages else browser.new_page()

        # Step 1: Ensure logged in
        if not wait_for_login(page):
            return ""

        # Step 2: New chat
        start_new_chat(page)

        # Step 3: Select model (best effort)
        if model:
            select_model(page, model)

        # Step 4: Submit prompt
        submit_prompt(page, prompt)

        # Step 5: Wait for response
        response = wait_for_response(page)

        # Step 6: Save
        if output_path and response:
            out = Path(output_path)
            out.parent.mkdir(parents=True, exist_ok=True)
            metadata = {
                "timestamp": datetime.now().isoformat(),
                "model": model,
                "prompt_length": len(prompt),
                "response_length": len(response),
            }
            out.write_text(
                f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
                encoding="utf-8",
            )
            print(f"[oracle] Saved to {out}")

        return response

    finally:
        browser.close()
        pw.stop()


def interactive_mode():
    """Just open ChatGPT logged in for manual use."""
    pw, browser = launch_browser(headless=False)
    page = browser.pages[0] if browser.pages else browser.new_page()

    if not wait_for_login(page):
        browser.close()
        pw.stop()
        return

    print("[oracle] Interactive mode. Browser is open. Press Ctrl+C to close.")
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass
    finally:
        browser.close()
        pw.stop()


def watch_mode(watch_dir: str, model: str):
    """Watch directory for incoming prompts, process them automatically.

    Agent workflow:
      1. Agent writes prompt to <watch_dir>/pending/<id>.md
      2. This service picks it up, submits to ChatGPT, saves to <watch_dir>/done/<id>.md
      3. Agent polls <watch_dir>/done/ for results

    Run from desktop terminal:
      python chatgpt_oracle.py --watch oracle/ --model o3-mini-high
    """
    watch = Path(watch_dir)
    pending = watch / "pending"
    done = watch / "done"
    pending.mkdir(parents=True, exist_ok=True)
    done.mkdir(parents=True, exist_ok=True)

    print(f"[oracle] Watch mode: monitoring {pending}/")
    print(f"[oracle] Results will be saved to {done}/")
    print(f"[oracle] Agents should write prompts to {pending}/<name>.md")
    print(f"[oracle] Press Ctrl+C to stop.\n")

    pw, browser = launch_browser(headless=False)
    page = browser.pages[0] if browser.pages else browser.new_page()

    if not wait_for_login(page):
        browser.close()
        pw.stop()
        return

    try:
        while True:
            # Scan for pending prompts
            for prompt_file in sorted(pending.glob("*.md")):
                name = prompt_file.stem
                out_file = done / f"{name}.md"

                if out_file.exists():
                    # Already processed — move pending file
                    prompt_file.unlink()
                    continue

                print(f"\n[oracle] Processing: {prompt_file.name}")
                prompt = prompt_file.read_text(encoding="utf-8")

                # New chat for each prompt
                start_new_chat(page)
                if model:
                    select_model(page, model)
                submit_prompt(page, prompt)
                response = wait_for_response(page)

                if response:
                    metadata = {
                        "timestamp": datetime.now().isoformat(),
                        "model": model,
                        "source": str(prompt_file),
                        "prompt_length": len(prompt),
                        "response_length": len(response),
                    }
                    out_file.write_text(
                        f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
                        encoding="utf-8",
                    )
                    print(f"[oracle] Saved: {out_file}")
                else:
                    # Write error marker
                    out_file.write_text("<!-- oracle: ERROR - no response -->\n", encoding="utf-8")
                    print(f"[oracle] ERROR: no response for {prompt_file.name}")

                # Remove from pending
                prompt_file.unlink()

            time.sleep(3)

    except KeyboardInterrupt:
        print("\n[oracle] Shutting down.")
    finally:
        browser.close()
        pw.stop()


def main():
    parser = argparse.ArgumentParser(
        description="ChatGPT Pro web oracle",
        epilog="""
Modes:
  --prompt/--prompt-file  One-shot: submit prompt, get response, exit
  --watch <dir>           Service: watch dir/pending/ for prompts, auto-process
  --interactive           Manual: just open logged-in ChatGPT browser

Agent integration (watch mode):
  1. Start service:  python chatgpt_oracle.py --watch oracle/
  2. Agent writes:   oracle/pending/p2_fredholm.md
  3. Service processes and saves: oracle/done/p2_fredholm.md
  4. Agent reads result from oracle/done/
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--prompt-file", type=Path, help="Read prompt from file")
    parser.add_argument("--prompt", type=str, help="Inline prompt string")
    parser.add_argument("--output", type=str, help="Save response to file")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"Model to select (default: {DEFAULT_MODEL})")
    parser.add_argument("--interactive", action="store_true",
                        help="Open ChatGPT for manual use")
    parser.add_argument("--watch", type=str, metavar="DIR",
                        help="Watch mode: monitor DIR/pending/ for prompts")
    parser.add_argument("--headless", action="store_true",
                        help="Run without visible browser (experimental)")
    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.watch:
        watch_mode(args.watch, args.model)
        return

    # One-shot mode
    if args.prompt_file:
        if not args.prompt_file.exists():
            print(f"Error: {args.prompt_file} not found", file=sys.stderr)
            sys.exit(1)
        prompt = args.prompt_file.read_text(encoding="utf-8")
    elif args.prompt:
        prompt = args.prompt
    else:
        print("Error: provide --prompt-file, --prompt, --watch, or --interactive",
              file=sys.stderr)
        sys.exit(1)

    response = run_oracle(prompt, args.output, args.model, args.headless)

    if not args.output and response:
        print("\n" + "=" * 60)
        print("RESPONSE:")
        print("=" * 60)
        print(response)

    sys.exit(0 if response else 1)


if __name__ == "__main__":
    main()
