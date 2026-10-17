#!/usr/bin/env python3
"""Regressions and exact replay checks of the stored enclosure endpoints.

The historical cache is consulted ONLY by this diagnostic, never by certify.py.
This checker does not replace the analytic quadrature proof.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse, importlib.util, json
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('certify',here/'certify.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
I=c.I

def endpoints(a):return F(a['lower']),F(a['upper'])
def main():
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--refinement',type=Path);ap.add_argument('--cache',type=Path);args=ap.parse_args()
 r=json.loads(args.certificate.read_text())
 assert r['status']=='RATIONAL_INTERVAL_SOURCE_CERTIFICATE_ANALYTIC_LINK_NOT_YET_LEAN'
 # Exact interval regressions: signed products, reciprocal and zero exclusion.
 s=I(-2,3)*I(-5,7);assert (s.l,s.u)==(F(-15),F(21))
 s=1/I(2,4);assert (s.l,s.u)==(F(1,4),F(1,2))
 try:1/I(-1,1)
 except AssertionError:pass
 else:raise AssertionError('division across zero was accepted')
 assert c.polynomials(4)[4]==list(map(F,['1/16','-39','166','-112','16']))
 A=[I(*endpoints(v)) for v in r['source_moments']]
 cs,hs,ps,B=c.eliminate(A)
 # Replaying after outward serialization can only be a tiny enlargement.
 tol=F(1,10**60)
 for a,b in zip(ps,r['pivots']):
  l,u=endpoints(b);assert a.l<=u and l<=a.u and abs(a.l-l)<tol and abs(a.u-u)<tol
 assert ps[3].l>F(1666,10**29) and ps[3].u<F(1667,10**29)
 gap=B-cs[9];assert gap.l>F(9203,10**31) and gap.u<F(9204,10**31)
 if args.refinement:
  rr=json.loads(args.refinement.read_text());assert rr['grid']==2*r['grid'] and rr['order']==r['order']
  for k in ['source_moments','pivots','characteristic','moments']:
   for a,b in zip(r[k],rr[k]):
    l,u=endpoints(a);ll,uu=endpoints(b);assert l<=ll<=uu<=u,(k,l,u,ll,uu)
 if args.cache:
  cache=json.loads(args.cache.read_text())
  for k,a in enumerate(A):
   q=F(cache['moments'][str(k)])/4**k;assert a.l<q<a.u
 print('PASS: exact endpoint replay, signed arithmetic, zero-denominator rejection, derivative recurrence, positive pivot and threshold gap')
 if args.refinement:print('PASS: all source/moment/pivot intervals contain their refined enclosures')
 if args.cache:print('DIAGNOSTIC ONLY: preserved cache lies inside the source enclosures; cache was not a certificate input')
if __name__=='__main__':main()
