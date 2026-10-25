#!/usr/bin/env python3
"""Read saved data only: source hashes and SAME-MOMENT numerical regression.
No new source campaign, spectral solve, pivot certificate or physical bridge.
"""
from pathlib import Path
from decimal import Decimal, localcontext
import csv,hashlib,json,subprocess
root=Path(__file__).resolve().parent
repo=Path('/home/thlinux/momentos')
run_path=repo/'native_jet_exploration/vm_campaign/vm-n40-reference/run.json'
csv_path=repo/'native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv'
readme=repo/'native_jet_exploration/vm_campaign/README.md'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
assert sha(run_path)=='9267df79f0b6c38508d790a14aca6e79bad16cc009518b4a8a881a13c07006ad'
assert sha(csv_path)=='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
run=json.loads(run_path.read_text())
source_hashes={}
for name,digest in run['source_sha256'].items():
    source=run_path.parent/'source'/Path(name).name
    assert sha(source)==digest,name
    source_hashes[name]=digest
with csv_path.open() as stream:rows=list(csv.DictReader(stream))
assert len(rows)==64 and len(run['moments'])==80
with localcontext() as ctx:
    ctx.prec=800
    errors=[]
    for row in rows:
        j=int(row['k']);a=Decimal(row['canonical_h']);b=Decimal(run['moments'][j])
        errors.append((abs(a-b)/max(abs(a),abs(b)),j))
    worst,index=max(errors)
    digits=int(-worst.log10())
    assert digits>=313
result={
    'status':'FINITE_NUMERICAL_REGRESSION_ONLY',
    'momentos_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
    'momentos_status':subprocess.check_output(['git','status','--porcelain=v1'],cwd=repo,text=True).strip(),
    'readme_sha256':sha(readme),'run_sha256':sha(run_path),'canonical_csv_sha256':sha(csv_path),
    'source_sha256':source_hashes,'saved_moments':len(run['moments']),
    'compared_moments':len(rows),'worst_relative_error':str(worst),
    'worst_index':index,'relative_agreement_digits':digits,
    'first_three_canonical_moments':[run['moments'][j] for j in range(3)],
    'raw_moment_zero_not_canonical':run['raw_moments'][0],
    'historical_vm_directory_exists':Path('/home/thlinux/native-jet-vm-20260930').exists(),
    'physical_incident_return_or_prime_readout_columns_saved':False,
    'limitations':['No interval certificate','No infinite operator limit',
      'Monic recurrence normalization tests signs; it does not derive them',
      'No geometric equality of the proposed finite boundary product B_N',
      'The source states needed for a Green/prime-atlas intertwiner are absent']}
(root/'evidence/vm-campaign-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS: {len(source_hashes)} saved source hashes; {len(rows)} canonical moments; {digits} relative digits; no new campaign.')
