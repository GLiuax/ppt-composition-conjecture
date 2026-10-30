"""Record source identities and check that all project modules are compiled."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
modules = {p.stem for p in (root / 'PPTQubit').glob('*.lean')}
entry = (root / 'PPTQubit.lean').read_text()
script = (root / 'verify-cached.sh').read_text()
imports = set(re.findall(r'^import PPTQubit\.(\w+)$', entry, re.M))
builds = set(re.findall(r'lean -o "\$ppt_build/PPTQubit/(\w+)\.olean"', script))
assert modules == imports == builds, (modules - imports, modules - builds, imports - modules, builds - modules)
files = sorted([root / 'PPTQubit.lean', *root.glob('PPTQubit/*.lean'),
                root / 'lean-toolchain', root / 'lakefile.lean', root / 'LICENSE',
                root / 'verify-cached.sh', root / 'audit.sh', *root.glob('audit/*.lean'),
                *root.glob('audit/*.py'), root / 'audit/dependency-cache-sha256.json',
                root / 'audit/dependency-cache-keys.tsv', root / 'audit/dependency-audit.json'])
manifest = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
manuscript_name = 'A Qubit Forbids Entanglement Swapping between PPT Links.tex'
# Support both the research workspace and the public repository layout.
manuscript_candidates = [root / '../../manuscript/qubit-main' / manuscript_name,
                         root / '../..' / manuscript_name]
for manuscript in manuscript_candidates:
    if manuscript.is_file():
        manifest['manuscript_sha256'] = hashlib.sha256(manuscript.read_bytes()).hexdigest()
        break
print(f'Inventory: {len(modules)} project modules, all imported and rebuilt.')
print(json.dumps(manifest, indent=2, sort_keys=True))
