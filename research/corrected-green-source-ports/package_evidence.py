#!/usr/bin/env python3
"""Preserve successful Lean logs, checked source hashes and compressed zone evidence."""
import argparse,gzip,hashlib,json,re
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--validation-log',type=Path,required=True)
a=ap.parse_args()
r=Path(__file__).resolve().parent;e=r/'evidence'
s=a.validation_log.read_text()
end='PASS: corrected Green physical ports and exact seven-jet realization'
if not s.rstrip().endswith(end):raise SystemExit('Complete successful validation sentinel absent')
expected={p.stem for p in r.glob('*.lean')}
passed=set(re.findall(r'^PASS: ([A-Za-z][A-Za-z0-9]*)$',s,re.M))
if expected!=passed:raise SystemExit(f'Module mismatch: {expected-passed}, {passed-expected}')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((e/'source-manifest.json').read_text())
for name,digest in m['lean_sources'].items():
 if sha(r/name)!=digest:raise SystemExit('Changed checked source '+name)
(e/'validation.log').write_text(s)
logs=['root-build.log','foundation-audit.log','geometry-audit.log','analysis-audit.log']
for name in logs:(e/(name+'.gz')).write_bytes(gzip.compress((e/name).read_bytes(),mtime=0))
record={'status':'pass','command':'bash research/corrected-green-source-ports/audit-corrected-green-source-ports.sh',
 'public_roots':len((r/'public-roots.txt').read_text().splitlines()),
 'modules':[{ 'name':n,'status':'pass','log_sha256':sha(e/(n+'.log'))} for n in sorted(expected)],
 'zone_and_root_logs':{n:sha(e/n) for n in logs}}
(e/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: packaged {len(expected)} modules and compressed root/zone logs')
