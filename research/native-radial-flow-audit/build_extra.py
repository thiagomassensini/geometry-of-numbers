from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent;repo=root.parents[1]
paths=json.loads((root/'extra-source-schedule.json').read_text());records={}
verify_only='--verify-existing' in sys.argv
prior=json.loads((root/'evidence/extra-upstream.json').read_text())['modules'] if verify_only else {}
for i,rel in enumerate(paths):
 source=repo/rel
 assert source.read_bytes()==subprocess.check_output(['git','show','83d035b5714c2cbadcd7f24bb50dd507b1fafe30:'+rel],cwd=repo)
 print(str(i+1)+'/'+str(len(paths))+' '+source.stem,flush=True)
 if not verify_only:
  subprocess.run(['bash','compile_module.sh',source.stem,str(source)],cwd=root,check=True)
 obj=source.parent/'.cache'/(source.stem+'.olean')
 records[source.stem]={'source':rel,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'olean_sha256':hashlib.sha256(obj.read_bytes()).hexdigest()}
 if verify_only:
  assert records[source.stem]==prior[source.stem],source.stem
 (root/'evidence/extra-upstream.json').write_text(json.dumps({'modules':records},indent=2)+'\n')
print('PASS: '+str(len(paths))+' unchanged interval-source ancestors '+('verified against recorded hashes.' if verify_only else 'freshly compiled.'),flush=True)
