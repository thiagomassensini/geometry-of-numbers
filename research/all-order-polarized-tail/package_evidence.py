#!/usr/bin/env python3
"""Package completed compiler/audit logs with source and dependency hashes."""
import gzip
import hashlib
import json
from pathlib import Path
import sys

from verify_provenance import BASE, DEPENDENCIES, head, pins

research, repo, operator, evidence = map(Path, sys.argv[1:])
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
sources = {f.name: sha(f) for f in sorted(research.glob('*.lean'))}
dependencies = {}
for folder in DEPENDENCIES:
    for f in sorted((repo/'research'/folder).glob('*.lean')):
        dependencies[str(f.relative_to(repo))] = sha(f)
manifest = {
    'base': BASE, 'validated_head': head(repo), 'operator_head': head(operator),
    'lean_toolchain': (repo/'lean-toolchain').read_text().strip(), 'pins': pins(repo),
    'lean_sources': sources, 'dependency_sources': dependencies,
    'dependency_build': 'reused existing audited caches; every new module compiled afresh',
    'legacy_without_source_manifest': ['material-pivot-certificate', 'material-central-calibration'],
    'cached_import_hashes': {str(f.relative_to(repo/'.lake/build')): sha(f)
        for folder in DEPENDENCIES for f in sorted((repo/'.lake/build/research'/folder).glob('*.olean'))},
}
(evidence/'source-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
for name in ['root-build.log', 'foundation-audit.log', 'geometry-audit.log', 'analysis-audit.log']:
    path = evidence/name
    path.with_suffix(path.suffix+'.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    path.unlink()
logs = {f.name: sha(f) for f in sorted(evidence.iterdir()) if f.suffix in ('.log', '.gz')}
result = {
    'status': 'pass', 'command': 'bash research/all-order-polarized-tail/audit-all-order-polarized-tail.sh',
    'public_roots': len((research/'public-roots.txt').read_text().splitlines()),
    'modules': 7, 'root_build': 'lake build --wfail',
    'zones': ['foundation', 'geometry', 'analysis'], 'logs': logs,
}
(evidence/'validation.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS: source/dependency hashes and completed validation manifest')
