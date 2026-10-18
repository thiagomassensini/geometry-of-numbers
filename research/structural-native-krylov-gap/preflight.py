from pathlib import Path
from fractions import Fraction
from decimal import Decimal,localcontext
import csv,hashlib,json
folder=Path(__file__).resolve().parent
path=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
moments={}
with path.open() as stream:
    for row in csv.DictReader(stream):
        k=int(row['k'])
        if k<3:moments[k]=Fraction(row['canonical_h'])
        if len(moments)==3:break
with localcontext() as c:
    c.prec=50
    ratio=moments[2]/moments[1]
    ratio_decimal=str(Decimal(ratio.numerator)/Decimal(ratio.denominator))
r=dict(status='FINITE STORED DECIMAL CHECK ONLY; NOT A LEAN INPUT',path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),rows_used=[0,1,2],column='canonical_h',two_over_one=ratio_decimal,quarter=str(Decimal(1)/4),strict_inequality=4*moments[2]<moments[1])
assert r['strict_inequality']
(folder/'evidence/preflight.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
