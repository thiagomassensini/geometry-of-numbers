#!/usr/bin/env python3
"""Package logs only after the complete Lean validation actually succeeds."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--validation-log', type=Path, required=True)
ap.add_argument('--reuse-pr22', action='store_true')
a = ap.parse_args()
r = Path(__file__).resolve().parent
e = r / 'evidence'
s = a.validation_log.read_text()
sentinel = 'PASS: integral certificate, fourth pivot, explicit transitive axiom guards and regressions'
if not s.rstrip().endswith(sentinel):
    raise SystemExit('Complete successful validation sentinel absent')
expected = {p.stem for p in r.glob('*.lean') if p.stem not in {'DumpNodeCache', 'DumpTaylorCache'}}
passed = set(re.findall(r'^PASS: ([A-Za-z][A-Za-z0-9]*)$', s, re.M))
if expected != passed:
    raise SystemExit(f'Module mismatch: missing={expected-passed}; extra={passed-expected}')
manifest = json.loads((e / 'source-manifest.json').read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for name, digest in manifest['lean_sources'].items():
    if sha(r / name) != digest:
        raise SystemExit('Changed checked source: ' + name)
(e / 'validation.log').write_text(s)
records = [{'module': name, 'status': 'pass', 'log_sha256': sha(e / (name + '.log'))}
           for name in sorted(expected)]
command = 'bash research/material-integral-certificate/audit-material-integral-certificate.sh'
if a.reuse_pr22:
    command = 'CARRY_INTEGRAL_REUSE_PR22=1 ' + command
result = {'status': 'pass', 'command': command,
          'lean_warning_as_error': True,
          'public_roots': len((r / 'public-roots.txt').read_text().splitlines()),
          'module_builds': records,
          'root_and_zone_logs': {name: sha(e / name) for name in
              ['root-build.log', 'foundation-audit.log', 'geometry-audit.log', 'analysis-audit.log']}}
(e / 'build-results.json').write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS: packaged {len(records)} module builds, source hashes and root/zone evidence')
