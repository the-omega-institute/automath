# Automath ChatGPT Oracle CDP Worker

This worker replaces the Tampermonkey ChatGPT Oracle tab with a local Chrome
DevTools Protocol worker. It keeps the existing Automath `oracle_server.py`
protocol and does not change publication gates.

## Install

```powershell
cd D:\omega\automath\tools\chatgpt-oracle\cdp-worker
npm install
```

## Start Chrome Profile

Use one dedicated Chrome profile and one CDP port. The launcher opens five
ChatGPT tabs in the same profile, marked with `?oracle=1` through `?oracle=5`.
Log in to ChatGPT once in this shared profile.

```powershell
powershell -ExecutionPolicy Bypass -File ..\start_chrome_cdp_profile.ps1 -Port 9222
```

The CDP port is unauthenticated. The launcher binds it to `127.0.0.1`; do not
expose it to the network and do not reuse this profile for unrelated browsing.

## Start Workers

Run one worker process per Oracle tab. All five workers attach to the same CDP
port and bind themselves to their own `?oracle=N` tab.

```powershell
$env:AUTOMATH_AGENT_ID='oracle_1'; $env:CHROME_CDP_URL='http://127.0.0.1:9222'; npm start
$env:AUTOMATH_AGENT_ID='oracle_2'; $env:CHROME_CDP_URL='http://127.0.0.1:9222'; npm start
$env:AUTOMATH_AGENT_ID='oracle_3'; $env:CHROME_CDP_URL='http://127.0.0.1:9222'; npm start
$env:AUTOMATH_AGENT_ID='oracle_4'; $env:CHROME_CDP_URL='http://127.0.0.1:9222'; npm start
$env:AUTOMATH_AGENT_ID='oracle_5'; $env:CHROME_CDP_URL='http://127.0.0.1:9222'; npm start
```

By default the worker talks to `http://127.0.0.1:8765`. Override with
`AUTOMATH_ORACLE_URL` if the local Oracle server runs elsewhere.

## PDF Tasks

`oracle_server.py` converts submitted `pdf_path` files to `pdf_base64` and
`pdf_name` before dispatch. The CDP worker writes that payload to a temporary
PDF, uploads it through ChatGPT's file input with Playwright `setInputFiles`,
waits for the attachment/upload state to settle, sends the prompt, then deletes
the temporary file.

## Checks

```powershell
npm run check
```

The repository also has a static Python check at:

```powershell
python ..\tests\test_cdp_worker_static.py
```
