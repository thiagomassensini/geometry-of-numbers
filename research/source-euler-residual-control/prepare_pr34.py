#!/usr/bin/env python3
"""Extract and recompile only the immutable source-box witnesses of PR34."""
import hashlib,json,os,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
repo=root.parent.parent
revision="da58f044c1c75bd828951bfb41614a6e7b8b465e"
modules=["SourceTwentySix","SourceCoefficients","CenteredLogRecurrence",
         "CenteredReferenceData","CenteredEvaluation","CenteredMomentBoxes","EvenTrialData"]
source=root/".cache/pr34/source"
cache=source.parent
source.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env["PATH"]="/home/thlinux/.elan/bin:"+env["PATH"]
operator=repo.parent/"carry-self-adjoint-operator"
base_lp=subprocess.check_output(["lake","env","printenv","LEAN_PATH"],cwd=operator,env=env,text=True).strip()
legacy=["sixth-odd-twelve-sources","sixth-even-source-schur","theta-fifth-odd-pattern",
        "critical-source-return","return-block-compatibility","corrected-green-source-ports",
        "material-integral-certificate","prime-camera-schur","material-pivot-certificate"]
env["LEAN_PATH"]=":".join([str(cache),str(repo/".lake/build/lib/lean")]+
    [str(repo/".lake/build/research"/s) for s in legacy]+[base_lp])
manifest={}
for name in modules:
    blob=subprocess.check_output(["git","show",f"{revision}:research/seventh-even-centered-source/{name}.lean"],cwd=repo)
    path=source/(name+".lean");path.write_bytes(blob)
    manifest[name]={"sha256":hashlib.sha256(blob).hexdigest(),"bytes":len(blob)}
    print("Recompile immutable PR34 source-box module: "+name,flush=True)
    subprocess.run(["lean","-DwarningAsError=true",f"--root={source}","-o",str(cache/(name+".olean")),str(path)],cwd=operator,env=env,check=True)
(root/"evidence").mkdir(exist_ok=True)
(root/"evidence/pr34-source.json").write_text(json.dumps({"revision":revision,"modules":manifest},indent=2)+"\n")
