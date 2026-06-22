from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[3]
NYXID = ROOT / ".nyxid-oracle"
START_ALL = NYXID / "start-all.ps1"
START_WORKER = NYXID / "start-cdp-worker.ps1"


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


class NyxidOracleScriptsStaticTests(unittest.TestCase):
    def test_start_all_does_not_treat_any_live_pid_as_worker(self):
        src = read(START_ALL)

        self.assertIn('ProcessName -eq "node"', src)
        self.assertNotIn("[bool](Get-Process -Id ([int]$workerPidText)", src)

    def test_start_all_restarts_workers_when_token_file_is_newer(self):
        src = read(START_ALL)

        self.assertIn("$TokenFile", src)
        self.assertIn("$tokenMtime", src)
        self.assertIn("$workerStart", src)
        self.assertIn("$workerStart -ge $tokenMtime", src)

    def test_start_all_can_force_restart_recorded_workers(self):
        src = read(START_ALL)

        self.assertIn("[switch]$RestartWorkers", src)
        self.assertIn("Stop-Process -Id $workerPid -Force", src)

    def test_start_worker_uses_project_worker_token_file(self):
        src = read(START_WORKER)

        self.assertIn('[string]$TokenFile = "worker-token.txt"', src)
        self.assertIn("$ResolvedTokenFile = Join-Path $Root $ResolvedTokenFile", src)
        self.assertIn("$env:NYXID_WORKER_TOKEN_FILE = $ResolvedTokenFile", src)

    def test_start_worker_bypasses_proxy_for_local_chrome_cdp(self):
        src = read(START_WORKER)

        self.assertIn("$env:NO_PROXY", src)
        self.assertIn("127.0.0.1,localhost", src)
        self.assertIn('"http://127.0.0.1:$ChromePort"', src)
        self.assertNotIn("$version.webSocketDebuggerUrl", src)

    def test_start_worker_bootstraps_warp_proxy_without_wsl_cli(self):
        src = read(START_WORKER)

        self.assertIn("function Ensure-WarpHttpProxy", src)
        self.assertIn("warp-cli.exe", src)
        self.assertIn("warp-http-proxy.mjs", src)
        self.assertNotIn("$Wrapper --version", src)
        self.assertNotIn("nyxid-via-warp.ps1 --version", src)

    def test_start_worker_can_use_company_token_file(self):
        src = read(START_WORKER)
        start_all = read(START_ALL)

        self.assertIn("[string]$TokenFile", src)
        self.assertIn("company-chatgpt-pro-worker-token.txt", start_all)
        self.assertIn("$env:NYXID_WORKER_TOKEN_FILE = $ResolvedTokenFile", src)

    def test_start_all_can_start_share_workers_without_replacing_local_pool(self):
        src = read(START_ALL)

        self.assertIn("[switch]$StartShare", src)
        self.assertIn("$CompanyWorkerLabels", src)
        self.assertIn("company-chatgpt-pro-worker-token.txt", src)
        self.assertIn("-WorkerTokenFile $CompanyTokenFile", src)
        self.assertIn('"company_win_work_1"', src)
        self.assertIn('"company_win_work_2"', src)
        self.assertNotIn('"company_win_work_1.company"', src)
        self.assertNotIn('"company_win_work_2.company"', src)

    def test_start_worker_uses_tab_isolated_chatgpt_pages(self):
        src = read(START_WORKER)

        self.assertIn("worker-tab-isolated.mjs", src)
        self.assertIn("$env:NYXID_CHATGPT_TAB_STORAGE_MARKER = $SafeLabel", src)
        self.assertIn("$env:NYXID_CHATGPT_TAB_KEY_URL", src)
        self.assertIn("$env:NYXID_CHATGPT_TAB_URL_MATCH", src)
        self.assertIn("$env:NYXID_WORKER_SCRIPT_VERSION", src)

    def test_start_worker_normalizes_path_before_start_process(self):
        src = read(START_WORKER)

        self.assertIn("function Normalize-ProcessPathEnvironment", src)
        self.assertIn('[Environment]::SetEnvironmentVariable("PATH", $null, "Process")', src)
        self.assertIn('[Environment]::SetEnvironmentVariable("Path", $pathValue, "Process")', src)
        self.assertIn("Normalize-ProcessPathEnvironment", src)
        self.assertIn("$node = (Get-Command node.exe).Source", src)
        self.assertIn("Start-Process -WindowStyle Hidden -PassThru -WorkingDirectory $WorkerDir", src)

    def test_start_worker_rejects_labels_invalid_for_nyxid_worker_api(self):
        src = read(START_WORKER)

        self.assertIn("$Label -notmatch '^[A-Za-z0-9_-]{1,64}$'", src)
        self.assertIn("Worker label must be 1-64 chars", src)
