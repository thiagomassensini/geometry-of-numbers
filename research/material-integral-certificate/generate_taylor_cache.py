#!/usr/bin/env python3
"""Untrusted Taylor witnesses, checked entry-by-entry by QuadratureNodeCheck*.lean."""
import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('taylor-cache.json'));ap.add_argument('--out',type=Path,default=Path(__file__).with_name('QuadratureCacheData.lean'));a=ap.parse_args()
rows=json.loads(a.input.read_text());assert len(rows)==208
box=lambda v:'Box.finite ('+str(int(v[0]))+') ('+str(int(v[1]))+')'
s='''import TaylorNodeComputation

/-! Untrusted scalar Taylor witnesses. They depend only on source modes and
quadrature positions, never on a moment matrix or its desired sign. -/
namespace CarryIntegralCertificate
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def quadratureCoefficientData : ℕ → List (List Box)
'''
for m,count in enumerate([96,64,48]):
 vals=[r for r in rows if r['m']==m];assert [r['j'] for r in vals]==list(range(count))
 assert all(len(r['coefficients'])==16 and all(v is not None for v in r['coefficients']) for r in vals)
 s+=f'  | {m} => ['+',\n    '.join('['+','.join(box(v) for v in r['coefficients'])+']' for r in vals)+']\n'
s+='  | _ => []\n\ndef quadratureErrorData : ℕ → List Box\n'
for m in range(3):
 vals=[r for r in rows if r['m']==m];assert all(r['error'] is not None for r in vals)
 s+=f'  | {m} => ['+',\n    '.join(box(r['error']) for r in vals)+']\n'
s+='''  | _ => []

def cachedQuadratureCoefficient (m j r : ℕ) : Box :=
  (((quadratureCoefficientData m)[j]?.getD [])[r]?).getD .all

def cachedQuadratureError (m j : ℕ) : Box :=
  ((quadratureErrorData m)[j]?).getD .all

end CarryIntegralCertificate
'''
a.out.write_text(s)
