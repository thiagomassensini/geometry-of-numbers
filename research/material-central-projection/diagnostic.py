"""UNCERTIFIED floating diagnostic; never a premise of the Lean proofs.

Uses the original consecutive material differences and complete C2 cells
with centers 4k, left legs 4k-1 and right legs 4k+1. Tail errors are NOT
enclosed. The comparison h1 is a midpoint of existing raw theta intervals.
"""
import json
import math

gradient_cutoff = 1_000_000
cell_cutoff = 100_000
source_sq, clock_sq, crossing = 1.0, 0.0, 0.0
for n in range(1, gradient_cutoff + 1):
    gradient = 1 / math.sqrt(n + 1) - 1 / math.sqrt(n)
    clock = math.log(n + 1) / math.sqrt(n + 1) - math.log(n) / math.sqrt(n)
    source_sq += gradient * gradient
    clock_sq += clock * clock
    crossing += gradient * clock
beta, signal_derivative_im = 0.0, 0.0
for k in range(1, cell_cutoff + 1):
    center = 4 * k
    beta += 1 / math.sqrt(center - 1) - 2 / math.sqrt(center) + 1 / math.sqrt(center + 1)
    signal_derivative_im += (
        -math.log(center - 1) / math.sqrt(center - 1)
        + 2 * math.log(center) / math.sqrt(center)
        - math.log(center + 1) / math.sqrt(center + 1)
    )
signal = 1 + beta
source_sq += beta * beta
clock_sq += signal_derivative_im * signal_derivative_im
crossing -= beta * signal_derivative_im
energy = (clock_sq - crossing * crossing / source_sq) / (2 * signal * signal)
a = (7767507 / 15625000 + 19884837 / 40000000) / 2
b = (574269 / 25000000 + 22974587 / 1000000000) / 2
c = (2962661 / 1000000000 + 740861 / 250000000) / 2
print(json.dumps({
    "status": "UNCERTIFIED_DIAGNOSTIC_ONLY",
    "gradient_cutoff": gradient_cutoff,
    "cell_cutoff": cell_cutoff,
    "projected_firstJet_energy_approx": energy,
    "h1_refined_box_midpoint_approx": b * b / (4 * a * a) - c / (12 * a),
    "warning": "Floating partial sums without tail enclosures; not a proof or certified interval."
}, indent=2))
