#!/usr/bin/env python3
"""Emit untrusted source-node witnesses; Lean checks every equality to the source program."""
import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('node-cache.json'));ap.add_argument('--out',type=Path,default=Path(__file__).with_name('NodeCacheData.lean'));a=ap.parse_args()
rows=json.loads(a.input.read_text());assert len(rows)==211
s='''import SourceComputation

/-! Cached arithmetic witnesses for the same theta program. Neither these
numbers nor the VM that produced them are trusted: ArgNodeChecks and
ModeNodeChecks verify every entry by kernel reduction. No moments are inputs. -/
namespace CarryIntegralCertificate
set_option autoImplicit false

def thetaCertificateCellCount : ℕ → ℕ
  | 0 => 96 | 1 => 64 | 2 => 48 | _ => 0
'''
for field,name in [('q','argumentNodeData'),('f','modeNodeData')]:
 s+=f'\ndef {name} : ℕ → List Box\n'
 for m,count in enumerate([97,65,49]):
  vals=[r for r in rows if r['m']==m];assert [r['j'] for r in vals]==list(range(count))
  assert all(r[field] is not None for r in vals)
  s+=f'  | {m} => ['+',\n    '.join('Box.finite ('+str(int(r[field][0]))+') ('+str(int(r[field][1]))+')' for r in vals)+']\n'
 s+='  | _ => []\n'
s+='''
def cachedArgumentNode (m j : ℕ) : Box := (argumentNodeData m)[j]?.getD .all

def cachedModeNode (m j : ℕ) : Box := (modeNodeData m)[j]?.getD .all

/-- Same formula as modeBox, with the separately checked argument witness. -/
def modeNodeComputation (m j : ℕ) : Box :=
  ((Box.point 2).mul (((gridBox j 64).div (.point 2)).exp)).div
    ((cachedArgumentNode m j).exp)

end CarryIntegralCertificate
'''
a.out.write_text(s)
