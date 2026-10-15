import GeometryOfNumbers.Geometry.IntegerCameraIncidence
import GeometryOfNumbers.Analysis.PrimeResidualDepthCrosswalk
import GeometryOfNumbers.Analysis.RealDepthMass
import Mathlib.Tactic.NormNum

/-! Discrete Mathlib crosswalks live downstream of the Init-only geometry.
Depth is still survival of the original residual tower. Factorization is used
only through the existing equivalence, never to redefine that relation. -/
namespace GeometryOfNumbers.Analysis
open Geometry
set_option autoImplicit false

theorem primeCamera_maximal_depth_iff {p n k : Nat} (hp : Nat.Prime p) (hn : n ≠ 0) :
    (HasCarryDepthAtLeast p n k ∧ ¬ HasCarryDepthAtLeast p n (k + 1)) ↔
      k = n.factorization p := by
  rw [primeResidualDepth_iff_le_factorization hp hn,
    primeResidualDepth_iff_le_factorization hp hn]
  omega

/-- Removing the scale of one camera preserves ALL residual thresholds in a
coprime camera. The horizontal core can therefore have positive other-depth. -/
theorem integerCamera_other_depth_iff {b q n k l : Nat}
    (hb : 0 < b) (hq : 0 < q) (hqb : Nat.Coprime q b)
    (hk : HasCarryDepthAtLeast b n k) :
    HasCarryDepthAtLeast q n l ↔
      HasCarryDepthAtLeast q (integerCameraTowerCell b n k).core l := by
  rw [hasCarryDepthAtLeast_iff_dvd_pow _ _ _ hq,
    hasCarryDepthAtLeast_iff_dvd_pow _ _ _ hq]
  conv_lhs => rw [← integerCameraTowerCell_reconstruction b n k hb hk]
  exact (hqb.pow l k).dvd_mul_left

theorem primeCamera_other_depth_iff {p q n k l : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hk : HasCarryDepthAtLeast p n k) :
    HasCarryDepthAtLeast q n l ↔
      HasCarryDepthAtLeast q (integerCameraTowerCell p n k).core l :=
  integerCamera_other_depth_iff hp.pos hq.pos
    ((Nat.coprime_primes hq hp).2 hpq.symm) hk

/-- Maximal depth excludes divisibility of the core by the base. This part
needs no primality; coprimality of core/base is a further prime consequence. -/
theorem integerCamera_maximal_core_not_dvd {b n k : Nat} (hb : 0 < b)
    (hk : HasCarryDepthAtLeast b n k)
    (hnext : ¬ HasCarryDepthAtLeast b n (k + 1)) :
    ¬ b ∣ (integerCameraTowerCell b n k).core := by
  rintro ⟨t, ht⟩
  apply hnext
  apply (hasCarryDepthAtLeast_iff_dvd_pow b n (k + 1) hb).2
  refine ⟨t, ?_⟩
  calc
    n = b ^ k * (integerCameraTowerCell b n k).core :=
      (integerCameraTowerCell_reconstruction b n k hb hk).symm
    _ = b ^ (k + 1) * t := by rw [ht, pow_succ, Nat.mul_assoc]

theorem primeCamera_maximal_core_coprime {p n k : Nat} (hp : Nat.Prime p)
    (hk : HasCarryDepthAtLeast p n k)
    (hnext : ¬ HasCarryDepthAtLeast p n (k + 1)) :
    Nat.Coprime p (integerCameraTowerCell p n k).core :=
  hp.coprime_iff_not_dvd.2 (integerCamera_maximal_core_not_dvd hp.pos hk hnext)

/-- Positive quantities have simultaneous maximal prime-camera presentations.
The original integer is their shared center; no legs are identified. -/
theorem primeCamera_common_maximal_presentations {p q n : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hn : n ≠ 0) :
    ∃ k l,
      (HasCarryDepthAtLeast p n k ∧ ¬ HasCarryDepthAtLeast p n (k + 1)) ∧
      (HasCarryDepthAtLeast q n l ∧ ¬ HasCarryDepthAtLeast q n (l + 1)) ∧
      IntegerCameraIncidence (integerCameraTowerCell p n k) .center (n : Int) ∧
      IntegerCameraIncidence (integerCameraTowerCell q n l) .center (n : Int) := by
  let k := n.factorization p
  let l := n.factorization q
  have hk := (primeCamera_maximal_depth_iff hp hn (k := k)).2 rfl
  have hl := (primeCamera_maximal_depth_iff hq hn (k := l)).2 rfl
  exact ⟨k, l, hk, hl, integerCamera_common_integer p q n k l hp.pos hq.pos hk.1 hl.1⟩

set_option maxRecDepth 4096 in
theorem primeCamera72_depths_and_cores :
    (HasCarryDepthAtLeast 2 72 3 ∧ ¬ HasCarryDepthAtLeast 2 72 4) ∧
      (HasCarryDepthAtLeast 3 72 2 ∧ ¬ HasCarryDepthAtLeast 3 72 3) ∧
      integerCameraTowerCell 2 72 3 = integerCamera72Two ∧
      integerCameraTowerCell 3 72 2 = integerCamera72Three ∧
      HasCarryDepthAtLeast 3 (integerCameraTowerCell 2 72 3).core 2 ∧
      HasCarryDepthAtLeast 2 (integerCameraTowerCell 3 72 2).core 3 := by
  simp only [hasCarryDepthAtLeast_iff_dvd_pow _ _ _ (by decide : 0 < 2),
    hasCarryDepthAtLeast_iff_dvd_pow _ _ _ (by decide : 0 < 3)]
  decide

/-- Maximal base-4 depth of 8 has core 2, which is NOT coprime to 4. -/
theorem compositeCamera_maximal_not_coprime_canary :
    HasCarryDepthAtLeast 4 8 1 ∧ ¬ HasCarryDepthAtLeast 4 8 2 ∧
      ¬ Nat.Coprime 4 (integerCameraTowerCell 4 8 1).core := by
  simp only [hasCarryDepthAtLeast_iff_dvd_pow _ _ _ (by decide : 0 < 4)]
  decide

theorem integerCamera72_local_masses :
    realDepthMass 2 3 (by decide) = 1 / 8 ∧
      realDepthMass 3 2 (by decide) = 1 / 9 ∧
      realDepthMass 2 3 (by decide) ≠ realDepthMass 3 2 (by decide) := by
  simp only [realDepthMass_eq_one_div_pow]
  norm_num

end GeometryOfNumbers.Analysis
