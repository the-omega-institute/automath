from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKER = ROOT / "cdp-worker" / "worker.mjs"
PACKAGE = ROOT / "cdp-worker" / "package.json"
LAUNCHER = ROOT / "start_chrome_cdp_profile.ps1"


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cdp_worker_uses_real_chrome_cdp_and_local_automath_protocol():
    src = read(WORKER)

    assert 'from "playwright-core"' in src
    assert "chromium.connectOverCDP(CDP_URL)" in src
    assert "http://127.0.0.1:8765" in src
    assert "/api/v1/oracle/worker" not in src
    assert "Authorization" not in src
    assert "NYXID_WORKER_TOKEN" not in src


def test_cdp_worker_identifies_parallel_agents_by_label():
    src = read(WORKER)

    assert 'AUTOMATH_AGENT_ID' in src
    assert 'process.env.AUTOMATH_AGENT_ID || "oracle_1"' in src
    assert "function agentTabMarker" in src
    assert "getChatPage(context, AGENT_ID)" in src
    assert "/task?agent=" in src
    assert "agent_id: AGENT_ID" in src
    assert "assigned_agent" in src


def test_cdp_worker_tracks_new_assistant_turn_to_avoid_stale_results():
    src = read(WORKER)

    assert "assistantCount()" in src
    assert "beforeCount" in src
    assert "count <= beforeCount" in src
    assert "count > beforeCount ? text : \"\"" in src
    assert "waiting_response" in src


def test_cdp_worker_uploads_pdf_attachments_before_prompt_send():
    src = read(WORKER)

    assert "pdf_path" in src
    assert "attachPdfIfPresent" in src
    assert "input[type='file']" in src
    assert "setInputFiles" in src
    assert "pathToFileURL" in src


def test_cdp_worker_reports_extraction_failures_without_marking_stale_success():
    src = read(WORKER)

    assert "ERROR: empty extraction" in src
    assert "ERROR: " in src
    assert "/result" in src
    assert "chatgpt_url" in src


def test_cdp_worker_has_node_package_and_syntax_check_script():
    pkg = read(PACKAGE)

    assert '"type": "module"' in pkg
    assert '"playwright-core"' in pkg
    assert '"check": "node --check worker.mjs"' in pkg


def test_windows_launcher_supports_shared_profile_multi_tab():
    src = read(LAUNCHER)

    assert "param(" in src
    assert "$Port" in src
    assert "$Agents" in src
    assert "--remote-debugging-port=$Port" in src
    assert "--remote-debugging-address=127.0.0.1" in src
    assert "--user-data-dir=$ProfilePath" in src
    assert ".chrome-chatgpt-cdp-profile" in src
    assert "foreach ($AgentId in $Agents)" in src
    assert "chatgpt.com" in src
