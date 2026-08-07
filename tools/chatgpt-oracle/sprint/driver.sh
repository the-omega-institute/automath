#!/bin/bash
# Self-driving sprint loop: harvest -> verify -> integrate -> recompile -> gate on PDF freshness -> next round
cd /d/omega/automath
D=/d/omega/automath/tools/chatgpt-oracle/sprint
PUB=/d/omega/automath/papers/publication
W=".nyxid-oracle/nyxid-via-warp.ps1"
nyx(){ MSYS_NO_PATHCONV=1 powershell.exe -ExecutionPolicy Bypass -File "$W" "$@" 2>&1 | sed 's/\r//'; }
declare -A S=( [A2]=2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa [A3]=2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds [A4]=2026_prime_languages_finite_state_obstructions_monatshefte [A5]=2026_finite_parts_dynamical_zeta_shifts_finite_type_etds [A6]=2026_finite_window_zeckendorf_fibers_discrete_thermodynamics_tams [A7]=2026_upper_fibers_witness_covers_fibonacci_apparition_fq [A8]=2026_detector_shells_click_record_kms_jphyscomm )

for tick in $(seq 1 400); do
  ts=$(date +%H:%M:%S); acted=0
  for t in A2 A3 A4 A5 A6 A7 A8; do
    slug="${S[$t]}"; d="$PUB/$slug"
    rnd=$(cat "$D/round_${t}" 2>/dev/null || echo 2)
    # 1) harvest pending oracle task
    tid=$(cat "$D/task_${t}" 2>/dev/null)
    if [ -n "$tid" ] && [ ! -f "$D/result_${t}_r${rnd}.md" ]; then
      r=$(nyx oracle result "$tid"); n=${#r}
      # terminal failure: release the slot and roll the round back so it is re-sent
      if echo "$r" | grep -qE "Task failed|Task was cancelled"; then
        : > "$D/task_${t}"; rm -f "$D/sent_${t}_r${rnd}"
        [ "$rnd" -gt 1 ] && echo $((rnd-1)) > "$D/round_${t}"
        echo "[$ts] $t r$rnd FAILED upstream -> rolled back, will resend"; acted=1
        continue
      fi
      if [ "$n" -gt 800 ] && ! echo "$r" | grep -q "Task is dispatched"; then
        printf '%s' "$r" > "$D/result_${t}_r${rnd}.md"
        cp "$D/result_${t}_r${rnd}.md" "$d/artifacts/oracle_sprint_${t}_r${rnd}.md"
        cvj=$(nyx oracle result "$tid" --output json | grep -oE "conv_[a-f0-9]+" | head -1)
        [ -n "$cvj" ] && echo "$cvj" > "$D/conv_${t}"
        sed "s/<TAG>/${t}_r${rnd}/g" "$D/judge_template.txt" > "$D/judge_${t}_r${rnd}.txt"
        nohup codex exec --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check -C "$d" - < "$D/judge_${t}_r${rnd}.txt" > "/tmp/judge_${t}_r${rnd}_out.txt" 2>&1 &
        echo "[$ts] $t r$rnd harvested+verify-dispatched"; acted=1
      fi
      continue
    fi
    # 2) submit next round when verification done AND pdf rebuilt after that round's reply
    nf="$d/next_${t}_r${rnd}.txt"
    if [ -f "$D/result_${t}_r${rnd}.md" ] && [ -f "$nf" ] && [ ! -f "$D/sent_${t}_r$((rnd+1))" ]; then
      if [ "$d/main.pdf" -nt "$d/artifacts/oracle_sprint_${t}_r${rnd}.md" ]; then
        touch "$D/sent_${t}_r$((rnd+1))"
        cv=$(cat "$D/conv_${t}" 2>/dev/null)
        if [ -n "$cv" ]; then CONVARG=(--conversation "$cv"); else CONVARG=(--new-conversation); fi
        out=$(nyx oracle ask company-chatgpt-pro --file "/mnt/d/omega/automath/papers/publication/$slug/next_${t}_r${rnd}.txt" --pdf "/mnt/d/omega/automath/papers/publication/$slug/main.pdf" --model chatgpt-pro "${CONVARG[@]}" --tag "sprint_${t}_r$((rnd+1))" --client-ref "sprint_${t}_r$((rnd+1))_$(date +%s)" --no-wait)
        ntid=$(echo "$out" | grep -oE "[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}" | head -1)
        ncv=$(echo "$out" | grep -oE "conv_[a-f0-9]+" | head -1)
        [ -n "$ncv" ] && echo "$ncv" > "$D/conv_${t}"
        if [ -n "$ntid" ]; then
          echo "$ntid" > "$D/task_${t}"; echo $((rnd+1)) > "$D/round_${t}"
          echo "[$ts] $t -> round $((rnd+1)) submitted (${ntid:0:8})"; acted=1; sleep 30
        else
          rm -f "$D/sent_${t}_r$((rnd+1))"
          if echo "$out" | grep -q "quota_exceeded"; then
            echo "[$ts] $t deferred: pool full, backing off 300s"; sleep 300
          else
            echo "[$ts] $t submit failed: $(echo "$out" | tr '\n' ' ' | cut -c1-160)"; sleep 60
          fi
        fi
      else
        echo "[$ts] $t r$rnd GATED: pdf not rebuilt yet"
      fi
    fi
  done
  pend=0
  for t in A2 A3 A4 A5 A6 A7 A8; do
    rr=$(cat "$D/round_${t}" 2>/dev/null || echo 3)
    [ -f "$D/result_${t}_r${rr}.md" ] || pend=$((pend+1))
  done
  echo "[$ts] tick $tick pending_harvest=$pend"
  if [ "$pend" -eq 0 ]; then echo "[$ts] ALL HARVESTED -- finish mode complete, exiting"; break; fi
  sleep 120
done
