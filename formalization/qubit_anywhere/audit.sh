#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
lean --version
python3 audit/check-cache.py
python3 audit/inventory.py
PPT_AUDIT=1 bash verify-cached.sh
python3 audit/inventory.py
printf '%s\n' 'Full audit passed.'
