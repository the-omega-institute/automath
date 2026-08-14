#!/bin/bash
cd /d/omega/automath
DIR=/d/omega/automath/tools/chatgpt-oracle/sprint
W=".nyxid-oracle/nyxid-via-warp.ps1"
nyx() { MSYS_NO_PATHCONV=1 powershell.exe -ExecutionPolicy Bypass -File "$W" "$@" 2>/dev/null | sed 's/\r//'; }
for tick in $(seq 1 300); do
  if [ -f "$DIR/sessions_r2.tsv" ]; then
    while IFS=$'\t' read -r tag slug task; do
      [ -z "$task" ] && continue
      [ -f "$DIR/result_${tag}_r2.md" ] && continue
      r=$(nyx oracle result "$task")
      n=${#r}
      if [ "$n" -gt 800 ] && ! echo "$r" | grep -q "Task is dispatched"; then
        printf '%s' "$r" > "$DIR/result_${tag}_r2.md"
        echo "[tick $tick] R2-HARVESTED $tag ($n chars)"
      elif echo "$r" | grep -qi "extraction_failure\|Task failed"; then
        echo "[tick $tick] R2-FAILED $tag"
      fi
    done < "$DIR/sessions_r2.tsv"
  fi
  jd=$(ls "$DIR"/../../../papers/publication/*/next_*.txt 2>/dev/null | wc -l)
  r2=$(ls "$DIR"/result_*_r2.md 2>/dev/null | wc -l)
  echo "[tick $tick] r2_harvested=$r2 next_files=$jd"
  sleep 60
done
