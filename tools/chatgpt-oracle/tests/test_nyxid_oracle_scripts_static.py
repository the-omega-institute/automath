from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[3]
NYXID = ROOT / ".nyxid-oracle"
SOURCE = ROOT / "tools" / "chatgpt-oracle" / "nyxid-worker"
START_ALL = SOURCE / "start-shared.ps1"
START_WORKER = SOURCE / "start-worker.ps1"
WORKER = SOURCE / "worker.mjs"


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


class NyxidOracleScriptsStaticTests(unittest.TestCase):
    def test_start_all_does_not_treat_any_live_pid_as_worker(self):
        src = read(START_ALL)

        self.assertIn('ProcessName -eq "node"', src)
        self.assertIn("$details.CommandLine", src)

    def test_start_all_uses_only_three_fixed_company_workers(self):
        src = read(START_ALL)

        self.assertIn('"company_win_work_1", "company_win_work_2", "company_win_work_3"', src)
        self.assertIn("company-chatgpt-pro-worker-token.txt", src)
        self.assertNotIn('"tab_1"', src)

    def test_start_all_can_force_restart_recorded_workers(self):
        src = read(START_ALL)

        self.assertIn("[switch]$RestartWorkers", src)
        self.assertIn("Stop-Process -Id ([int]$pidText) -Force", src)

    def test_start_worker_uses_company_worker_token_file(self):
        src = read(START_WORKER)

        self.assertIn("company-chatgpt-pro-worker-token.txt", src)
        self.assertIn("$env:NYXID_WORKER_TOKEN_FILE = $TokenFile", src)

    def test_start_worker_bypasses_proxy_for_local_chrome_cdp(self):
        src = read(START_WORKER)

        self.assertIn("$env:NO_PROXY", src)
        self.assertIn("127.0.0.1,localhost", src)
        self.assertIn('"http://127.0.0.1:$ChromePort"', src)
        self.assertNotIn("$version.webSocketDebuggerUrl", src)

    def test_start_worker_never_bootstraps_or_restarts_warp(self):
        src = read(START_WORKER)

        self.assertNotIn("warp-cli", src)
        self.assertNotIn("Ensure-WarpHttpProxy", src)
        self.assertIn("run start-shared.ps1 explicitly", src)

    def test_start_all_uses_company_pool_without_local_pool(self):
        src = read(START_ALL)

        self.assertIn("$WorkerLabels", src)
        self.assertIn("company-chatgpt-pro-worker-token.txt", src)
        self.assertIn('"company_win_work_1"', src)
        self.assertIn('"company_win_work_2"', src)
        self.assertIn('"company_win_work_3"', src)

    def test_start_worker_uses_tab_isolated_chatgpt_pages(self):
        src = read(START_WORKER)

        self.assertIn("worker.mjs", src)
        self.assertIn("$env:NYXID_CHATGPT_TAB_STORAGE_MARKER = $SafeLabel", src)
        self.assertIn("$env:NYXID_CHATGPT_TAB_URL_MATCH", src)
        self.assertIn("$env:NYXID_WORKER_SCRIPT_VERSION", src)

    def test_start_worker_uses_explicit_node_source_and_working_directory(self):
        src = read(START_WORKER)

        self.assertIn("$node = (Get-Command node.exe).Source", src)
        self.assertIn("Start-Process -WindowStyle Hidden -PassThru -WorkingDirectory $PSScriptRoot", src)

    def test_start_worker_restricts_labels_to_fixed_company_workers(self):
        src = read(START_WORKER)

        self.assertIn('[ValidateSet("company_win_work_1", "company_win_work_2", "company_win_work_3")]', src)

    def test_worker_uses_current_chat_work_dom_and_followup_contract(self):
        src = read(WORKER)

        self.assertIn('getByRole("radio", { name: modeLabel, exact: true })', src)
        self.assertIn('getAttribute("data-state")', src)
        self.assertIn("verifyFollowupConversation", src)
        self.assertIn("collectArtifacts", src)
        self.assertIn("setInputFiles", src)
        self.assertNotIn("article[data-testid^='conversation-turn']", src)

    def test_worker_extracts_final_answer_not_reasoning_blocks(self):
        src = read(WORKER)

        self.assertIn("function isReasoningBlock", src)
        self.assertIn("function messageContentCandidates", src)
        self.assertIn("function extractAssistantContent", src)
        self.assertIn('[data-testid^="conversation-turn"]', src)
        self.assertIn("[data-message-author-role='assistant'] [data-testid*='message']", src)
        self.assertIn("[data-message-author-role='assistant'] .markdown", src)

    def test_scrape_turns_scan_all_role_nodes_in_turn(self):
        src = read(WORKER)

        self.assertIn('const roleEls = Array.from(w.querySelectorAll("[data-message-author-role]"));', src)
        self.assertNotIn('const roleEl = w.querySelector("[data-message-author-role]");', src)

    def test_local_entry_points_are_thin_delegates(self):
        start_all = read(NYXID / "start-all.ps1")
        start_worker = read(NYXID / "start-cdp-worker.ps1")

        self.assertIn("tools\\chatgpt-oracle\\nyxid-worker\\start-shared.ps1", start_all)
        self.assertIn("tools\\chatgpt-oracle\\nyxid-worker\\start-worker.ps1", start_worker)
        self.assertNotIn("warp-cli", start_worker)
