#!/bin/bash
cd /d/omega/automath
DIR=/d/omega/automath/tools/chatgpt-oracle/sprint
PUB=/d/omega/automath/papers/publication
W=".nyxid-oracle/nyxid-via-warp.ps1"
nyx() { MSYS_NO_PATHCONV=1 powershell.exe -ExecutionPolicy Bypass -File "$W" "$@" 2>/dev/null | sed 's/\r//'; }

for tick in $(seq 1 300); do
  while IFS=$'\t' read -r tag slug task; do
    [ -z "$task" ] && continue
    [ -f "$DIR/result_${tag}.md" ] && continue
    r=$(nyx oracle result "$task")
    n=${#r}
    if [ "$n" -gt 800 ] && ! echo "$r" | grep -q "Task is dispatched"; then
      printf '%s' "$r" > "$DIR/result_${tag}.md"
      echo "[tick $tick] HARVESTED $tag ($n chars)"
      # capture conversation id for follow-up rounds
      conv=$(nyx oracle sessions --pool company-chatgpt-pro --limit 20 | grep -oE "conv_[a-f0-9]+" | head -1)
      echo -e "${tag}\t${conv}" >> "$DIR/convs.tsv"
      # AUTO-DISPATCH VERIFICATION (this is the point: verify, don't just implement)
      if [ -d "$PUB/$slug" ]; then
        mkdir -p "$PUB/$slug/artifacts"
        cp "$DIR/result_${tag}.md" "$PUB/$slug/artifacts/oracle_sprint_${tag}.md"
        sed "s/<TAG>/$tag/g" "$DIR/judge_template.txt" > "$DIR/judge_${tag}.txt"
        nohup codex exec --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check \
          -C "D:/omega/automath/papers/publication/$slug" - < "$DIR/judge_${tag}.txt" \
          > "$DIR/judge_${tag}_out.txt" 2>&1 &
        echo "[tick $tick] VERIFY-DISPATCHED $tag"
      fi
    elif echo "$r" | grep -qi "extraction_failure\|Task failed"; then
      grep -q "^$tag$" "$DIR/failed.txt" 2>/dev/null || echo "$tag" >> "$DIR/failed.txt"
      echo "[tick $tick] FAILED $tag (needs resubmit)"
    fi
  done < "$DIR/sessions_r1b.tsv"

  h=$(ls "$DIR"/result_*.md 2>/dev/null | wc -l)
  j=$(ls "$DIR"/judge_*_out.txt 2>/dev/null | wc -l)
  echo "[tick $tick] harvested=$h verify_jobs=$j"
  [ "$h" -ge 7 ] && [ "$j" -ge 7 ] && echo "ALL HARVESTED+VERIFYING" && break
  sleep 60
done
