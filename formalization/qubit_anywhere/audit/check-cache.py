"""Check this audit's pinned binary dependency snapshot before rebuilding."""
from pathlib import Path
import hashlib
import json
import os

root = Path(__file__).resolve().parents[1]
cache = Path(os.environ.get('PPT_MATHLIB_CACHE', '/private/tmp/ppt-lean-mathlib'))
expected = json.loads((root / 'audit/dependency-cache-sha256.json').read_text())
if not expected:
    raise SystemExit('Empty dependency audit manifest')
failures = []
for relative, digest in expected.items():
    path = cache / relative
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        failures.append(relative)
if failures:
    raise SystemExit('Dependency cache differs from the audited snapshot:\n' + '\n'.join(failures[:20]))
print(f'Dependency snapshot passed: {len(expected)} compiled files match the pinned-source cache archives.')
