# NyxID ChatGPT Shared Worker

This directory is the maintained source for the three Windows company workers.
Local tokens, PIDs, logs, Chrome profiles, and artifact spools remain under
`D:\omega\automath\.nyxid-oracle` and are not committed.

Run tests with `npm test`. Start the shared stack explicitly with
`start-shared.ps1`; individual workers never connect or restart Cloudflare WARP.
