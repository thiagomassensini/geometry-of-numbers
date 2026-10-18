import TenSourceReturn
import CarrySelfAdjointOperator.CompletedNativeLogCoefficientMajorant

/-! Uniform cutoff estimates for the actual synthesized source. The complex
pairing is kept before taking a diagonal or a real part. Coefficient energy
below is only an error-budget norm, never a replacement physical metric. -/
namespace CarrySourceTail
open CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open scoped BigOperators ComplexConjugate Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def rate : ℝ := 22/175

theorem rate_pos : 0 < rate := by norm_num [rate]
theorem rate_lt_one : rate < 1 := by norm_num [rate]
theorem denominator_pos : 0 < 1-rate^2 := by norm_num [rate]

/-- Rectangular, fully polarized pairing of the ORIGINAL logarithmic moments. -/
def sourcePair {n m : ℕ} (s : ℕ) (x : Fin n → ℂ) (y : Fin m → ℂ) : ℂ :=
  ∑ i, ∑ j, (h (i.val+j.val+s):ℂ)*conj (x i)*y j

def coefficientEnergy {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖^2
def weightedSize {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖*rate^i.val

theorem coefficientEnergy_nonneg {n : ℕ} (x : Fin n → ℂ) :
    0 ≤ coefficientEnergy x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem weightedSize_nonneg {n : ℕ} (x : Fin n → ℂ) :
    0 ≤ weightedSize x := Finset.sum_nonneg (fun _ _ => by positivity [rate_pos.le])

/-- The bound is unconditional: it does not assume the sign of ANY moment. -/
theorem source_entry_bound (s i j : ℕ) :
    |h (i+j+s)| ≤ rate^(s+1)*rate^i*rate^j := by
  calc
    _ ≤ rate^(i+j+s+1)-(1/25:ℝ)^(i+j+s+1) :=
      canonicalCompletedNativeLogDerivativeMoment_sharp_decay _
    _ ≤ rate^(i+j+s+1) := sub_le_self _ (by positivity)
    _ = _ := by rw [show i+j+s+1=(s+1)+i+j by omega, pow_add, pow_add]

theorem sourcePair_norm_le {n m : ℕ} (s : ℕ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    ‖sourcePair s x y‖ ≤ rate^(s+1)*weightedSize x*weightedSize y := by
  calc
    _ ≤ ∑ i, ∑ j, ‖(h (i.val+j.val+s):ℂ)*conj (x i)*y j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j,
        (rate^(s+1)*rate^i.val*rate^j.val)*‖x i‖*‖y j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (source_entry_bound s i.val j.val) (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by
      simp only [weightedSize, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem geometric_weight_sum (n : ℕ) :
    (∑ i : Fin n, (rate^i.val)^2) ≤ 1/(1-rate^2) := by
  have hg : ∀ n : ℕ, (∑ i ∈ Finset.range n, (rate^2)^i)*(1-rate^2) = 1-(rate^2)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  have he : (∑ i : Fin n, (rate^i.val)^2) = ∑ i ∈ Finset.range n, (rate^2)^i := by
    calc
      _ = ∑ i : Fin n, (rate^2)^i.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← pow_mul, Nat.mul_comm i.val 2, pow_mul]
      _ = _ := Fin.sum_univ_eq_sum_range _ _
  rw [he]
  apply (le_div_iff₀ denominator_pos).mpr
  rw [hg]
  exact sub_le_self _ (by positivity [rate_pos.le])

theorem weightedSize_sq_le {n : ℕ} (x : Fin n → ℂ) :
    weightedSize x^2 ≤ coefficientEnergy x/(1-rate^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖x i‖)
    (fun i => rate^i.val)
  calc
    _ ≤ coefficientEnergy x*(∑ i : Fin n, (rate^i.val)^2) := hc
    _ ≤ coefficientEnergy x*(1/(1-rate^2)) :=
      mul_le_mul_of_nonneg_left (geometric_weight_sum n) (coefficientEnergy_nonneg x)
    _ = _ := by ring

/-- All four ordered blocks. The two arguments and the two tail lengths
remain independent; no crossing has been erased by this identity. -/
theorem sourcePair_append {N M L : ℕ} (s : ℕ)
    (x y : Fin N → ℂ) (a : Fin M → ℂ) (b : Fin L → ℂ) :
    sourcePair s (Fin.append x a) (Fin.append y b) =
      sourcePair s x y + sourcePair (s+N) x b +
        sourcePair (s+N) a y + sourcePair (s+2*N) a b := by
  simp only [sourcePair, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib, two_mul,
    Nat.add_comm, Nat.add_left_comm, add_assoc]
  abel

theorem coefficientEnergy_append {N M : ℕ} (x : Fin N → ℂ) (a : Fin M → ℂ) :
    coefficientEnergy (Fin.append x a) = coefficientEnergy x+coefficientEnergy a := by
  simp only [coefficientEnergy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- An explicit error budget, not a positive metric or a fitted scale. -/
def cutoffError (s N : ℕ) : ℝ :=
  rate^(s+1)*(rate^N+rate^(2*N))/(1-rate^2)

theorem cutoffError_nonneg (s N : ℕ) : 0 ≤ cutoffError s N := by
  exact div_nonneg (by positivity [rate_pos.le]) denominator_pos.le

end
end CarrySourceTail
