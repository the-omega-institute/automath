# Replay Guide

This package does not vendor the SAIR-EQT2 judge. Replay requires a separate checkout of the official judge at the commit recorded in `manifests/judge_snapshot.json`.

1. Clone the judge:

```sh
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2 /path/eqt2-stage2
cd /path/eqt2-stage2
git checkout 6805e2323018fbd8a85f41ca09fc33d74d5a02a5
```

2. Prepare the judge environment using the judge repository's setup instructions.

3. Validate certificate JSONL shape:

```sh
python3 scripts/check_cert_jsonl.py certs/guided_certs.jsonl
python3 scripts/check_cert_jsonl.py certs/blind_spike_certs.jsonl
```

4. Replay an individual certificate by writing the selected manifest row's problem and answer payload to scratch files, then running:

```sh
python3 scripts/verify_one.py --judge-root /path/eqt2-stage2 /path/problem.json /path/answer.json
```

5. Use `manifests/certificate_replay_manifest.jsonl` as the replay ledger. Each row records the certificate file, line index, mode, chosen verdict, judge policy, and judge commit expected for replay.

The recorded acceptance claim is local-runner acceptance under `DEFAULT_PROOF_POLICY`, not hosted leaderboard submission.
