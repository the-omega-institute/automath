#!/bin/bash
cd /d/omega/automath
DIR=/d/omega/automath/tools/chatgpt-oracle/sprint
W=".nyxid-oracle/nyxid-via-warp.ps1"
nyx() { MSYS_NO_PATHCONV=1 powershell.exe -ExecutionPolicy Bypass -File "$W" "$@" 2>/dev/null | sed 's/\r//'; }
while true; do
  ts=$(date +%H:%M:%S)
  # harvest round-2 oracle replies
  if [ -f "$DIR/sessions_r2.tsv" ]; then
    while IFS=$'\t' read -r tag slug task; do
      [ -z "$task" ] && continue
      [ -f "$DIR/result_${tag}_r2.md" ] && continue
      r=$(nyx oracle result "$task"); n=${#r}
      if [ "$n" -gt 800 ] && ! echo "$r" | grep -q "Task is dispatched"; then
        printf '%s' "$r" > "$DIR/result_${tag}_r2.md"; echo "[$ts] R2-HARVEST $tag ($n)"
      elif echo "$r" | grep -qi "extraction_failure\|Task failed"; then echo "[$ts] R2-FAIL $tag"; fi
    done < "$DIR/sessions_r2.tsv"
  fi
  r2=$(ls "$DIR"/result_*_r2.md 2>/dev/null | wc -l)
  nx=$(ls /d/omega/automath/papers/publication/*/next_*.txt 2>/dev/null | wc -l)
  cx=$(ps aux 2>/dev/null | grep -c "[n]ode")
  echo "[$ts] r2=$r2 next_files=$nx node_procs=$cx"
  sleep 90
done
