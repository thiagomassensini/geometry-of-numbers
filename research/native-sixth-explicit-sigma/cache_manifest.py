from pathlib import Path
import hashlib,json
old=Path('/home/thlinux/geometry-of-numbers-native-sixth-odd-relative-anchor')
new=Path('/home/thlinux/geometry-of-numbers-native-sixth-explicit-sigma')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=[]; mismatch=[]
for f in sorted(old.glob('research/*/.cache/*.olean')):
 if not f.is_file(): continue
 rel=f.relative_to(old); g=new/rel
 if not g.is_file() or sha(f)!=sha(g): mismatch.append(str(rel))
 else: entries.append({'file':str(rel),'sha256':sha(f)})
for rel in [Path('.lake/build/research/sixth-odd-twelve-sources/OddSourceBoxes.olean'),Path('.lake/build/research/sixth-odd-twelve-sources/OddTrialData.olean'),Path('.lake/build/research/sixth-odd-twelve-sources/OddTrialPositivity.olean'),Path('.lake/build/research/theta-fifth-odd-pattern/FifthOddCertificate.olean')]:
 if not (new/rel).is_file() or sha(old/rel)!=sha(new/rel): mismatch.append(str(rel))
 else: entries.append({'file':str(rel),'sha256':sha(old/rel)})
out={'base_worktree':str(old),'checked_worktree':str(new),'compared_compiled_modules':len(entries),'mismatches':mismatch,'warning':'Byte identity to prior worktree only; this is not a clean recompilation of historical sources.','artifacts':entries}
(new/'research/native-sixth-explicit-sigma/evidence/reused-cache-manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'compared_compiled_modules':len(entries),'mismatches':mismatch}))
