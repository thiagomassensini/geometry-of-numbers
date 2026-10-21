#!/usr/bin/env python3
"""Diagnostic only: unchanged native canonical checkpoint, no recomputation."""
import argparse,csv,hashlib,json
from pathlib import Path
import mpmath as mp
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument("--checkpoint",default="/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv")
args=parser.parse_args()
p=Path(args.checkpoint)
fixture=root/"fixtures/canonical-checkpoint.json"
if p.exists():
    rows=list(csv.DictReader(p.open()))
    payload={"origin":str(p),"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),
             "column":"canonical_h","moments":[r["canonical_h"] for r in rows]}
    fixture.parent.mkdir(exist_ok=True)
    if fixture.exists():assert json.loads(fixture.read_text())==payload
    else:fixture.write_text(json.dumps(payload,indent=2)+"\n")
else:payload=json.loads(fixture.read_text())
results=[]
for precision in [300,450]:
    mp.mp.dps=precision
    h=[mp.mpf(x) for x in payload["moments"]]
    table=[]
    for n in range(1,min(32,len(h)//2)):
        A=mp.matrix([[h[i+j] for j in range(n)] for i in range(n)])
        b=mp.matrix([h[i+n] for i in range(n)])
        a=-mp.lu_solve(A,b)
        pivot=h[2*n]+sum(b[i]*a[i] for i in range(n))
        euler=h[0]*a[0]**2
        residual=max(abs(t) for t in A*a+b)
        table.append({"n":n,"pivot":mp.nstr(pivot,40),"constant_coefficient":mp.nstr(a[0],40),
                      "euler":mp.nstr(euler,40),"nonlinear_half":mp.nstr(pivot-euler,40),
                      "nonlinear_over_pivot":mp.nstr((pivot-euler)/pivot,32),
                      "solve_residual":mp.nstr(residual,8)})
    results.append({"dps":precision,"data":table})
for lo,hi in zip(results[0]["data"],results[1]["data"]):
    assert lo["pivot"]==hi["pivot"]
    assert lo["nonlinear_over_pivot"]==hi["nonlinear_over_pivot"]
# This is a regression from the SAME stored decimals, not an interval for the source.
assert mp.mpf(results[0]["data"][5]["pivot"])>0
assert mp.mpf(results[0]["data"][5]["nonlinear_half"])<0
out={"scope":"numerical diagnostic of stored canonical_h; no theta inclusion and no kernel claim",
     "source_sha256":payload["sha256"],"precision_comparison_digits":32,"results":results}
(root/"evidence").mkdir(exist_ok=True)
(root/"evidence/checkpoint-probe.json").write_text(json.dumps(out,indent=2)+"\n")
print("PASS: 31 residual directions at 300 and 450 DPS; first negative nonlinear finite part at n=6")
