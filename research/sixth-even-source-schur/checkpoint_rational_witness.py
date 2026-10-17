#!/usr/bin/env python3
"""Exact-rational Schur lower bound for a FINITE DECIMAL MOMENT CHECKPOINT.

Given the canonical_h decimals already exported by the Carry source, this
proves (using Fraction exact arithmetic) positivity ONLY for the rational
finite-decimal approximation. It is not a certificate for the theta integral.

Mathematics: for A>0, b, c, and an arbitrary rational trial x,
  sigma = c - b^T A^{-1} b
        = c - 2*b^T*x + x^T*A*x - r^T*A^{-1}*r,
  r=A*x-b.
Since ||A^{-1}||_2 <= ||A^{-1}||_infty = M (symmetric A),
  sigma >= q(x) - M * ||r||_2^2.
All calculations following the reading of the checkpoint are exact rationals.
"""
import argparse
import csv
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp


def matvec(a,x):
    return [sum((a[i][j]*x[j] for j in range(len(x))),Fraction(0)) for i in range(len(x))]


def dot(x,y):
    return sum((a*b for a,b in zip(x,y)),Fraction(0))


def ldl(a):
    n=len(a)
    lo=[[Fraction(int(i==j)) for j in range(n)] for i in range(n)]
    d=[Fraction(0)]*n
    for j in range(n):
        dj=a[j][j]-sum((lo[j][k]*lo[j][k]*d[k] for k in range(j)),Fraction(0))
        if dj<=0:
            raise ValueError(f'Old rational prefix is not positive definite, pivot {j}={dj}')
        d[j]=dj
        for i in range(j+1,n):
            lo[i][j]=(a[i][j]-sum((lo[i][k]*lo[j][k]*d[k] for k in range(j)),Fraction(0)))/dj
    return lo,d


def solve_ldl(lo,d,b):
    n=len(d)
    y=[]
    for i in range(n):
        y.append(b[i]-sum((lo[i][j]*y[j] for j in range(i)),Fraction(0)))
    z=[y[i]/d[i] for i in range(n)]
    x=[Fraction(0)]*n
    for i in range(n-1,-1,-1):
        x[i]=z[i]-sum((lo[j][i]*x[j] for j in range(i+1,n)),Fraction(0))
    return x


def fmt(q,precision=22):
    return mp.nstr(mp.mpf(q.numerator)/q.denominator,precision)


def witness(path,sector=0,n=5,digits=20,output=None):
    raw=Path(path).read_bytes()
    rows=list(csv.DictReader(raw.decode('utf-8').splitlines()))
    if not rows or 'canonical_h' not in rows[0]: raise ValueError('Expected canonical_h CSV')
    rows.sort(key=lambda r:int(r['k']))
    if [int(row['k']) for row in rows[:2*n+sector+1]]!=list(range(2*n+sector+1)):
        raise ValueError('Missing or duplicate moment indices')
    h=[Fraction(row['canonical_h']) for row in rows[:2*n+sector+1]]
    a=[[h[i+j+sector] for j in range(n)] for i in range(n)]
    b=[h[n+i+sector] for i in range(n)]
    c=h[2*n+sector]
    lo,d=ldl(a)
    exact_x=solve_ldl(lo,d,b)
    mp.mp.dps=max(100,digits+45)
    trial=[Fraction(mp.nstr(mp.mpf(x.numerator)/x.denominator,digits)) for x in exact_x]
    r=[t-u for t,u in zip(matvec(a,trial),b)]
    q=c-2*dot(b,trial)+dot(trial,matvec(a,trial))
    r2=dot(r,r)
    # Exact infinity norm of the symmetric rational inverse, an upper bound
    # on the 2-operator norm used in the rigorous finite rational inequality.
    inv_cols=[solve_ldl(lo,d,[Fraction(int(i==j)) for i in range(n)]) for j in range(n)]
    max_row_sum=max(sum((abs(inv_cols[j][i]) for j in range(n)),Fraction(0)) for i in range(n))
    lower=q-max_row_sum*r2
    actual=c-dot(b,exact_x)
    assert actual>0 if lower>0 else True
    assert lower<=actual<=q, 'Failed exact arithmetic Schur sandwich'
    # A provable *conditional* interval certificate: if EACH genuine source
    # moment lies within epsilon*abs(checkpoint_decimal), then all Hankel entries
    # inherit these errors (including their repeated/crossed occurrences).
    # This is a guarantee about any real moments in these intervals, not a
    # claim that theta integrations have already been enclosed there.
    RA=max(sum((abs(a[i][j]) for j in range(n)),Fraction(0)) for i in range(n))
    qweight=(abs(c)+2*sum((abs(trial[i])*abs(b[i]) for i in range(n)),Fraction(0))
             +sum((abs(trial[i])*abs(a[i][j])*abs(trial[j]) for i in range(n) for j in range(n)),Fraction(0)))
    rr1=sum((abs(y) for y in r),Fraction(0))
    rweight=sum((abs(b[i])+sum((abs(a[i][j])*abs(trial[j]) for j in range(n)),Fraction(0))
                 for i in range(n)),Fraction(0))
    interval_scenarios=[]
    for exponent in (20,24,25,26,27,28,30,35,40):
        eps=Fraction(1,10**exponent)
        denom=1-max_row_sum*eps*RA
        bound=None if denom<=0 else q-eps*qweight-(max_row_sum/denom)*(rr1+eps*rweight)**2
        interval_scenarios.append({'uniform_relative_radius':f'1e-{exponent}',
          'prefix_PD_control':denom>0,
          'rational_lower_bound':fmt(bound) if bound is not None else None,
          'conditional_schur_positive':bound is not None and bound>0})
    result={
        'input':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
        'kind':'EXACT_RATIONAL_TEST_ON_DECIMAL_CHECKPOINT_NOT_THETA_CERTIFICATE',
        'sector':sector,'old_prefix_dimension':n,'new_moment_index':2*n+sector,
        'trial_significant_digits':digits,
        'rational_old_prefix_positive':True,
        'trial_rational_vector':[str(x) for x in trial],
        'old_pivots_positive':True,
        'old_min_pivot':fmt(min(d)),
        'q_trial':fmt(q),'residual_norm_sq':fmt(r2),
        'inverse_inf_norm_upper_bound':fmt(max_row_sum),
        'certified_rational_lower_bound':fmt(lower),
        'rational_schur_exact':fmt(actual),
        'rational_lower_bound_positive':lower>0,
        'upper_correction_fraction':fmt(max_row_sum*r2/actual),
        'inequality_verified_by_exact_Fraction':True,
        'is_certificate_for_original_theta_integrals':False,
        'hypothetical_genuine_source_moment_interval_tests':interval_scenarios,
        'next_gate':'Replace decimal point inputs by rational intervals certified to enclose the original completed theta source, then propagate q and r bounds.'
    }
    if output: Path(output).write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    return result

if __name__=='__main__':
    pa=argparse.ArgumentParser(description=__doc__)
    pa.add_argument('--csv',required=True)
    pa.add_argument('--sector',type=int,default=0,choices=(0,1))
    pa.add_argument('--n',type=int,default=5)
    pa.add_argument('--digits',type=int,default=20)
    pa.add_argument('--output')
    args=pa.parse_args()
    if args.n<1 or args.digits<4:pa.error('n>=1 and digits>=4 required')
    result=witness(args.csv,args.sector,args.n,args.digits,args.output)
    print(json.dumps(result,indent=2,ensure_ascii=False))
