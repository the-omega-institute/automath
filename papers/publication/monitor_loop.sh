#!/bin/bash
# Continuous oracle monitor — runs every 5 minutes
cd /d/omega/automath/papers/publication
while true; do
    PYTHONIOENCODING=utf-8 python monitor_oracle.py --summary 2>&1
    echo "--- next check in 5 min ---"
    echo ""
    sleep 300
done
