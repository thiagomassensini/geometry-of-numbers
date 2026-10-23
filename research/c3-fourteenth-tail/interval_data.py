#!/usr/bin/env python3
"""Generate rational witnesses by exact arithmetic, never by mpmath.

Every proposed enclosure is rechecked against the certified evaluator in Lean.
The Python generator is not a trusted producer of mathematical assertions.
"""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import math

ROOT = Path(__file__).resolve().parent
SCALE = 10**30

def point(q):
    return Q(q), Q(q)

def rnd(a):
    l, h = a
    return Q(l.numerator*SCALE//l.denominator, SCALE), Q(h.numerator*SCALE//h.denominator+1, SCALE)

def add(a, b):
    return rnd((a[0]+b[0], a[1]+b[1]))

def neg(a):
    return -a[1], -a[0]

def sub(a, b):
    return add(a, neg(b))

def mul(a, b):
    v = [x*y for x in a for y in b]
    return rnd((min(v), max(v)))

def inv(a):
    assert a[0]>0 or a[1]<0
    return rnd((1/a[1], 1/a[0]))

def pow_(a, n):
    p = point(1)
    for _ in range(n):
        p = mul(p, a)
    return p

def sum_(items):
    p = point(0)
    for a in items:
        p = add(p, a)
    return p

def expand(a, e):
    return a[0]-e, a[1]+e

@lru_cache(None)
def unitlog(a):
    q = -sum(((1-a)**(j+1)/Q(j+1) for j in range(128)), Q(0))
    return rnd(expand(point(q), Q(1, 10**35)))

@lru_cache(None)
def log_(q, p):
    a = Q(q)/2**p
    assert Q(1, 2)<=a<=1
    return add(mul(point(p), neg(unitlog(Q(1, 2)))), unitlog(a))

def exp_(a):
    assert -4<=a[0]<=a[1]<=4
    return expand(sum_(mul(pow_(a, k), point(Q(1, math.factorial(k)))) for k in range(64)), Q(1, 10**30))

def wider(a, digits=24):
    s = 10**digits
    return Q(a[0].numerator*s//a[0].denominator, s), Q(a[1].numerator*s//a[1].denominator+1, s)

def rat(q):
    return f'({q.numerator}/{q.denominator})'

def leanbox(a):
    return '⟨'+rat(a[0])+','+rat(a[1])+'⟩'

def main():
    logs = [wider(log_(Q(n), n.bit_length())) for n in range(1, 206)]
    amplitudes = [wider(exp_(mul(point(Q(-1, 2)), l))) for l in logs]
    text = ['import ElementaryBoxes', 'namespace CarryC3Boxes',
            'set_option maxHeartbeats 10000000', 'set_option maxRecDepth 20000',
            'def sampleLogReference (n : Fin 205) : Box := !['+','.join(map(leanbox, logs))+'] n',
            'def sampleAmplitudeReference (n : Fin 205) : Box := !['+','.join(map(leanbox, amplitudes))+'] n',
            'theorem sample_log_normalization (n : Fin 205) :',
            '    (1/2:ℚ) ≤ (n.val+1:ℚ)/2^(Nat.log2 (n.val+1)+1) ∧',
            '      (n.val+1:ℚ)/2^(Nat.log2 (n.val+1)+1) ≤ 1 := by',
            '  fin_cases n <;> decide +kernel',
            'theorem sample_log_evaluator_check (n : Fin 205) :',
            '    (rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1)).Subset (sampleLogReference n) := by',
            '  fin_cases n <;> decide +kernel',
            'theorem sample_amplitude_range_check (n : Fin 205) :',
            '    -4 ≤ (bmul (Box.point (-1/2)) (sampleLogReference n)).lo ∧',
            '      (bmul (Box.point (-1/2)) (sampleLogReference n)).hi ≤ 4 := by',
            '  fin_cases n <;> decide +kernel',
            'theorem sample_amplitude_evaluator_check (n : Fin 205) :',
            '    (expBox (bmul (Box.point (-1/2)) (sampleLogReference n))).Subset (sampleAmplitudeReference n) := by',
            '  fin_cases n <;> decide +kernel',
            'theorem sample_log_reference_contains (n : Fin 205) :',
            '    (sampleLogReference n).Contains (Real.log (n.val+1:ℕ)) := by',
            '  apply Box.subset_contains (sample_log_evaluator_check n)',
            '  simpa only [Rat.cast_natCast,Rat.cast_add,Rat.cast_one,Nat.cast_add,Nat.cast_one] using',
            '    rational_log_box (n.val+1) (Nat.log2 (n.val+1)+1) (sample_log_normalization n)',
            'theorem sample_amplitude_reference_contains (n : Fin 205) :',
            '    (sampleAmplitudeReference n).Contains (Real.exp (-Real.log (n.val+1:ℕ)/2)) := by',
            '  apply Box.subset_contains (sample_amplitude_evaluator_check n)',
            '  have h := bmul_contains (Box.point_contains (-1/2)) (sample_log_reference_contains n)',
            '  have he : ((-1/2:ℚ):ℝ)*Real.log (n.val+1:ℕ) = -Real.log (n.val+1:ℕ)/2 := by norm_num; ring',
            '  rw [he] at h',
            '  exact exp_box h (sample_amplitude_range_check n).1 (sample_amplitude_range_check n).2',
            'end CarryC3Boxes']
    (ROOT/'SamplePrimitiveBoxes.lean').write_text('\n'.join(text)+'\n')
    print('Generated 205 rational log and amplitude witnesses; Lean must validate them.')

if __name__ == '__main__':
    main()
