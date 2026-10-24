#!/usr/bin/env python3
"""Reproduce reviewed user inputs; numerical probes never enter Lean proofs."""
from pathlib import Path
from fractions import Fraction
import csv
import json
import runpy
import mpmath as mp

root = Path(__file__).resolve().parent
inputs = root / "inputs"
out = root / "evidence"
out.mkdir(exist_ok=True)
ns = runpy.run_path(str(inputs / "investigar_compensacao_carry.py"))
result = {
    "camera": ns["check_camera_exact"](),
    "green": ns["check_green"](),
    "logclock": ns["check_logclock"](),
}
reference = json.loads((inputs / "experimento_compensacao_carry_20261024.json").read_text())
assert result["camera"] == reference["camera"]
for key in ["h0", "critical_eta", "J_threshold"]:
    assert abs(mp.mpf(result["green"][key]) - mp.mpf(reference["green"][key])) < mp.mpf("1e-24")
for left, right in zip(result["green"]["kappa_sweep"], reference["green"]["kappa_sweep"]):
    for key in ["total", "bulk", "mixed"]:
        assert abs(mp.mpf(left[key]) - mp.mpf(right[key])) < mp.mpf("1e-16")

mp.mp.dps = 80
rows = []
for kappa in [10, 100, 1000]:
    responses = [ns["response"](mp.j * (j + 1) / mp.mpf(kappa)) for j in [0, 1]]
    defect = mp.j * 2 * kappa * (mp.conj(responses[0]) + responses[1]) / 3
    assert abs(defect - 2 * kappa * (mp.im(responses[0]) - mp.im(responses[1])) / 3) < mp.mpf("1e-75")
    rows.append({"kappa": kappa, "response_values": [mp.nstr(r, 40) for r in responses],
                 "selfadjoint_compatibility_defect": mp.nstr(defect, 40)})

with (inputs / "Jacobi_Canonica_6x6_Valores.csv").open() as stream:
    data = list(csv.reader(stream))
matrix = [[Fraction(x) for x in row[1:]] for row in data[1:]]
assert len(matrix) == 6 and all(len(row) == 6 for row in matrix)
assert all(matrix[i][j] == matrix[j][i] for i in range(6) for j in range(6))
assert all(matrix[i][j] == 0 for i in range(6) for j in range(6) if abs(i-j) > 1)
pivots = []
for i in range(6):
    pivot = matrix[i][i] if i == 0 else matrix[i][i] - matrix[i][i-1]**2 / pivots[-1]
    assert pivot > 0
    pivots.append(pivot)
result["alignment"] = rows
result["rounded_jacobi_positive_rational_pivots"] = [str(p) for p in pivots]
result["scope"] = "Finite input camera Grams and rounded J; xi-based Green diagnostic; no source interval or all-order certificate."
(out / "uploaded-material-diagnostic.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
print("PASS: 100 exact period pairs, camera pivots, Green profiles, logclock crosses, 6 rounded-J pivots; nonzero alignment diagnostics")
