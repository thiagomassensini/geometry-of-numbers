#!/usr/bin/env python3
"""Arb-interval canaries: center/legs after prime-depth log differentiation.

These are scalar C2/Cp brackets, not completed F-moment Hankel forms.
Arb intervals are computed from rational integers, not measured zeros.
"""
from flint import arb,ctx
import json
from pathlib import Path
ctx.dps=110

def br2(fun,c):
    return fun(c-1)-2*fun(c)+fun(c+1)
def br5(fun,c):
    return sum((fun(c-r)+fun(c+r)-2*fun(c) for r in [1,2]),arb(0))
def f(n):
    return arb(1)/arb(n).sqrt()
def logf(n):
    return arb(n).log()*f(n)
def logn(n):
    return arb(n).log()
checks=[
 ("C2_half_power_c5",br2(f,5),"positive"),
 ("C2_log_weighted_half_c5",br2(logf,5),"negative"),
 ("C2_log_c5",br2(logn,5),"negative"),
 ("C5_half_power_c5",br5(f,5),"positive"),
 ("C5_log_weighted_half_c5",br5(logf,5),"negative"),
 ("C5_log_c5",br5(logn,5),"negative"),
]
data={}
for name,x,expect in checks:
    if expect=="positive": assert bool(x>0),name
    else:assert bool(x<0),name
    print(name,expect,x)
    data[name]={"value_interval":str(x),"sign_certified_for_decimal_rational_input":expect}
# 4,5,6 original log bracket = log(24/25), not a fresh zeta identity.
logratio=(arb(24)/arb(25)).log()
assert (br2(logn,5)-logratio).contains(0)
print("C2 log bracket at center5 is log(24/25)",logratio)
output=Path(__file__).resolve().parent.parent/"evidence"/"mangoldt_leg_center_arb_canaries.json"
output.write_text(json.dumps({
  "status":"SCALAR_LOCAL_C2_CP_BRACKET_ARBITRARY_PRECISION_INTERVAL_CANARY_NOT_NATIVE_HANKEL_SIGN",
  "precision_dps":ctx.dps,
  "inputs":"integer centers 5, radii 1 (C2) and 1,2 (C5), no zero heights",
  "source":"f=n^{-1/2}, g=log(n)*n^{-1/2}, log(n)",
  "checks":data},indent=2)+"\n")
print("EVIDENCE",output)
