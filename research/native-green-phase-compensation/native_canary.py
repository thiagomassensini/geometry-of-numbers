#!/usr/bin/env python3
"""Finite prefixes of the ORIGINAL material state; numerical evidence only.
No theta, canonical moment, zero, height or target Gram is an input.
There is NO certified error bound for the infinite tails in this script.
"""
from math import log,sqrt,fsum
from pathlib import Path
import json
levels=[]
for M in [1000,5000,20000,100000]:
    sample=[[log(n)**m/sqrt(n) for n in range(1,4*M+2)] for m in range(3)]
    gradient=[[s[j+1]-s[j] for j in range(len(s)-1)] for s in sample]
    boundary=[fsum(s[4*k+2]-2*s[4*k+3]+s[4*k+4] for k in range(M)) for s in sample]
    # Assemble the seed, whole material interior AND cell return first.
    vectors=[[1. if m==0 else 0.]+gradient[m]+[boundary[m]] for m in range(3)]
    ip=lambda x,y:fsum(a*b for a,b in zip(x,y))
    mass=ip(vectors[0],vectors[0]);mean=ip(vectors[0],vectors[1])/mass
    forcing=[b-mean*a for a,b in zip(vectors[0],vectors[1])]
    b=ip(forcing,forcing)
    mu=2*mean*b-ip(forcing,vectors[2])
    levels.append({'cells':M,'edges':4*M,'mass':mass,'kappa':mean,
                   'forcing_norm_squared':b,'chi_linear_coefficient':2*b,
                   'chi_t2_imaginary_coefficient_estimate':mu})
result={'status':'NUMERICAL_ONLY','certified_infinite_tail':False,
        'source':'Y_m = (delta_m0, first differences of log(n)^m/sqrt(n), whole C2 cell return)',
        'cell_addresses':'center 4(k+1), legs 4(k+1)-1 and 4(k+1)+1',
        'finite_projectors_only':'kappa and forcing are computed for each full finite prefix; not exact infinite w.',
        'formal_bridge':'PhaseJet.second_coefficient_physical; no numerical value is used in a Lean proof.',
        'levels':levels}
out=Path(__file__).resolve().parent/'evidence';out.mkdir(exist_ok=True)
(out/'native-phase-canary.json').write_text(json.dumps(result,indent=2)+'\n')
print('NUMERICAL ONLY: final finite-prefix phase coefficient =',levels[-1]['chi_t2_imaginary_coefficient_estimate'])
