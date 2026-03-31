#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ChatGPT Pro browser automation using undetected-chromedriver.

Uses the system Chrome with anti-detection patches to bypass Cloudflare.
Reuses an existing Chrome user profile (already logged into ChatGPT).

Setup (one-time):
    python chatgpt_browser.py --login
    # This opens Chrome for you to log in. Close it when done.

Usage:
    # Send a text prompt:
    python chatgpt_browser.py --prompt "Prove that ..." --output result.md

    # Upload PDF and send prompt:
    python chatgpt_browser.py --pdf paper.pdf --prompt "Review this paper" --output result.md

    # Use specific model:
    python chatgpt_browser.py --pdf paper.pdf --prompt "..." --model o3-mini-high --output result.md
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from datetime import datetime

PROFILE_DIR = Path(__file__).parent / ".chrome_profile"
CHATGPT_URL = "https://chatgpt.com"
DEFAULT_MODEL = "o3-mini-high"


def create_driver(headless: bool = False):
    """Create an undetected Chrome driver with persistent profile."""
    import undetected_chromedriver as uc

    options = uc.ChromeOptions()
    options.add_argument(f"--user-data-dir={PROFILE_DIR}")

    if headless:
        options.add_argument("--headless=new")

    driver = uc.Chrome(options=options, use_subprocess=True)
    return driver


def wait_for_element(driver, selector: str, timeout: int = 30):
    """Wait for an element to appear."""
    from selenium.webdriver.common.by import By
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC

    return WebDriverWait(driver, timeout).until(
        EC.presence_of_element_located((By.CSS_SELECTOR, selector))
    )


def wait_for_response_complete(driver, timeout: int = 600) -> str:
    """Wait for ChatGPT to finish responding and return the text.

    Detects completion by watching for the response to stop changing.
    """
    from selenium.webdriver.common.by import By

    start = time.time()
    last_text = ""
    stable_count = 0
    STABLE_THRESHOLD = 3  # must be stable for 3 consecutive checks

    print("[browser] Waiting for response...", end="", flush=True)

    while time.time() - start < timeout:
        try:
            # ChatGPT renders responses in markdown containers
            # Try multiple selectors for different ChatGPT UI versions
            response_els = driver.find_elements(By.CSS_SELECTOR,
                "[data-message-author-role='assistant'] .markdown")
            if not response_els:
                response_els = driver.find_elements(By.CSS_SELECTOR,
                    ".agent-turn .markdown")
            if not response_els:
                response_els = driver.find_elements(By.CSS_SELECTOR,
                    "[class*='response'] .markdown")

            if response_els:
                # Get the last response (most recent)
                current_text = response_els[-1].text.strip()

                if current_text and current_text == last_text:
                    stable_count += 1
                    if stable_count >= STABLE_THRESHOLD:
                        # Also check there's no "Stop generating" button
                        stop_btns = driver.find_elements(By.CSS_SELECTOR,
                            "button[aria-label='Stop generating']")
                        if not stop_btns:
                            print(f" done ({len(current_text)} chars)")
                            return current_text
                else:
                    stable_count = 0
                    last_text = current_text

                elapsed = int(time.time() - start)
                if elapsed % 30 == 0 and elapsed > 0:
                    print(f"\n[browser] Still generating... ({elapsed}s, {len(current_text)} chars)", end="", flush=True)

        except Exception:
            pass

        time.sleep(2)

    print(f"\n[browser] Timeout after {timeout}s")
    return last_text


def upload_and_send(driver, prompt: str, pdf_path: Path | None = None):
    """Upload a file (if any) and send a prompt to ChatGPT."""
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys

    # Upload PDF if provided
    if pdf_path and pdf_path.exists():
        print(f"[browser] Uploading {pdf_path.name}...")
        # Find the file input (hidden) and send the file path
        file_inputs = driver.find_elements(By.CSS_SELECTOR, "input[type='file']")
        if file_inputs:
            file_inputs[0].send_keys(str(pdf_path.resolve()))
            time.sleep(3)  # Wait for upload
            print(f"[browser] File uploaded")
        else:
            print("[browser] WARNING: Could not find file input, sending text only")

    # Find the prompt textarea and type
    print(f"[browser] Entering prompt ({len(prompt)} chars)...")
    textarea = None
    for selector in ["#prompt-textarea", "textarea[data-id]", "div[contenteditable='true']"]:
        els = driver.find_elements(By.CSS_SELECTOR, selector)
        if els:
            textarea = els[0]
            break

    if not textarea:
        print("[browser] ERROR: Could not find input textarea", file=sys.stderr)
        return

    # Clear and type prompt (using JavaScript for long text)
    driver.execute_script("""
        var el = arguments[0];
        var text = arguments[1];
        if (el.tagName === 'TEXTAREA' || el.tagName === 'INPUT') {
            el.value = text;
            el.dispatchEvent(new Event('input', {bubbles: true}));
        } else {
            el.innerText = text;
            el.dispatchEvent(new Event('input', {bubbles: true}));
        }
    """, textarea, prompt)

    time.sleep(1)

    # Click send button
    send_btns = driver.find_elements(By.CSS_SELECTOR,
        "button[data-testid='send-button'], button[aria-label='Send prompt']")
    if send_btns:
        send_btns[0].click()
    else:
        # Fallback: press Enter
        textarea.send_keys(Keys.RETURN)

    print("[browser] Prompt sent")


def login_mode():
    """Open browser for manual login."""
    print("[browser] Opening Chrome for login...")
    print("[browser] Please log into ChatGPT, then close the browser window.")
    driver = create_driver(headless=False)
    driver.get(CHATGPT_URL)
    input("[browser] Press Enter here after you've logged in and want to close... ")
    driver.quit()
    print("[browser] Login session saved. You can now use automated mode.")


def run_query(prompt: str, pdf_path: Path | None = None,
              output_path: Path | None = None, model: str = DEFAULT_MODEL,
              headless: bool = True):
    """Run a full query: open ChatGPT, upload file, send prompt, get response."""

    driver = create_driver(headless=headless)

    try:
        print(f"[browser] Opening ChatGPT...")
        driver.get(CHATGPT_URL)
        time.sleep(5)  # Wait for page load

        # Check if we're logged in
        page_text = driver.page_source
        if "Log in" in page_text and "Sign up" in page_text:
            print("[browser] ERROR: Not logged in. Run: python chatgpt_browser.py --login",
                  file=sys.stderr)
            driver.quit()
            sys.exit(1)

        # Select model if needed (ChatGPT model selector)
        # This varies by UI version, skip for now — uses default model

        # Upload file and send prompt
        upload_and_send(driver, prompt, pdf_path)

        # Wait for response
        response = wait_for_response_complete(driver, timeout=600)

        if response:
            print(f"[browser] Got response: {len(response)} chars")

            if output_path:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                metadata = {
                    "timestamp": datetime.now().isoformat(),
                    "model": model,
                    "prompt_length": len(prompt),
                    "response_length": len(response),
                }
                if pdf_path:
                    metadata["pdf"] = str(pdf_path)
                output_path.write_text(
                    f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
                    encoding="utf-8",
                )
                print(f"[browser] Saved to {output_path}")
            else:
                print("\n" + response)
        else:
            print("[browser] ERROR: No response received", file=sys.stderr)

    finally:
        driver.quit()

    return response


def main():
    parser = argparse.ArgumentParser(
        description="ChatGPT Pro browser automation (Cloudflare-resistant)",
    )
    parser.add_argument("--login", action="store_true",
                        help="Open browser for manual login (one-time setup)")
    parser.add_argument("--prompt", type=str, help="Prompt text")
    parser.add_argument("--prompt-file", type=Path, help="Read prompt from file")
    parser.add_argument("--pdf", type=Path, help="PDF to upload")
    parser.add_argument("--output", type=Path, help="Save response to file")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--visible", action="store_true",
                        help="Show browser window (default: headless)")
    args = parser.parse_args()

    if args.login:
        login_mode()
        return

    prompt = args.prompt
    if args.prompt_file:
        prompt = args.prompt_file.read_text(encoding="utf-8")

    if not prompt:
        print("Error: need --prompt or --prompt-file", file=sys.stderr)
        sys.exit(1)

    run_query(prompt, args.pdf, args.output, args.model, headless=not args.visible)


if __name__ == "__main__":
    main()
