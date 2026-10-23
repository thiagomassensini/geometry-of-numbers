import KernelBudget
import LiteralTailBounds

namespace CarrySourceBezout
open Filter Topology
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem responseCoefficient_even_zero (c : ℕ → ℂ) : responseCoefficient c false 0 = 0 := by
  simp [responseCoefficient, sourceResponse]

theorem responseCoefficient_even_succ (c : ℕ → ℂ) (n : ℕ) :
    responseCoefficient c false (n+1) = -((n+1:ℕ):ℂ)*c (n+1) := by
  simp [responseCoefficient, sourceResponse, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative, sourceSeries]
  ring

theorem responseCoefficient_odd (c : ℕ → ℂ) (n : ℕ) :
    responseCoefficient c true n = -((n+1:ℕ):ℂ)*c (n+1) := by
  simp [responseCoefficient, sourceResponse, PowerSeries.coeff_derivative, sourceSeries]
  ring

theorem responseCoefficient_tendsto (c : ℕ → ℕ → ℂ) (d : ℕ → ℂ)
    (hc : ∀ n, Tendsto (fun M => c M n) atTop (nhds (d n))) (b : Bool) (n : ℕ) :
    Tendsto (fun M => responseCoefficient (c M) b n) atTop (nhds (responseCoefficient d b n)) := by
  cases b
  · cases n with
    | zero => simpa only [responseCoefficient_even_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0:ℂ)) atTop (nhds 0))
    | succ n => simpa only [responseCoefficient_even_succ] using
        (hc (n+1)).const_mul (-((n+1:ℕ):ℂ))
  · simpa only [responseCoefficient_odd] using (hc (n+1)).const_mul (-((n+1:ℕ):ℂ))

theorem coefficientBudget_tendsto (c d : ℕ → ℕ → ℂ) (a e : ℕ → ℂ)
    (hc : ∀ n, Tendsto (fun M => c M n) atTop (nhds (a n)))
    (hd : ∀ n, Tendsto (fun M => d M n) atTop (nhds (e n))) (b : Bool) (i j : ℕ) :
    Tendsto (fun M => coefficientBudget (c M) (d M) b i j) atTop
      (nhds (coefficientBudget a e b i j)) := by
  unfold coefficientBudget
  apply Tendsto.add
  · apply tendsto_finsetSum
    intro k hk
    exact (hd (j-k)).norm.mul (responseCoefficient_tendsto c a hc b (i+k+1)).norm
  · apply tendsto_finsetSum
    intro k hk
    exact (responseCoefficient_tendsto c a hc b (j-k)).norm.mul (hd (i+k+1)).norm

theorem directionalBudget_tendsto (c d : ℕ → ℕ → ℂ) (a e : ℕ → ℂ)
    (hc : ∀ n, Tendsto (fun M => c M n) atTop (nhds (a n)))
    (hd : ∀ n, Tendsto (fun M => d M n) atTop (nhds (e n)))
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    Tendsto (fun M => directionalBudget (c M) (d M) b r x y) atTop
      (nhds (directionalBudget a e b r x y)) := by
  unfold directionalBudget
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((coefficientBudget_tendsto c d a e hc hd b i.val j.val).const_mul |x i|).mul_const |y j|

theorem literal_tail_tendsto_zero (n : ℕ) :
    Tendsto (fun M => literalTail M n) atTop (nhds 0) := by
  obtain ⟨C,hC,henv⟩ := literal_tail_jet_envelope
  have hm : Tendsto (fun M : ℕ => (M:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlim : Tendsto (fun M : ℕ => (C/((M:ℝ)+1))*16^n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero.comp hm).const_mul C).mul_const ((16:ℝ)^n)
  exact squeeze_zero_norm (fun M => henv M n) hlim

theorem literal_head_tendsto (n : ℕ) :
    Tendsto (fun M => literalHead M n) atTop (nhds (nativeC n : ℂ)) := by
  have he (M : ℕ) : literalHead M n = (nativeC n:ℂ)-literalTail M n := by
    have h := congrFun (literal_head_tail M) n
    simp only [Pi.add_apply] at h
    linear_combination -h
  simp_rw [he]
  simpa using (tendsto_const_nhds.sub (literal_tail_tendsto_zero n))

theorem responseCoefficient_zero (b : Bool) (n : ℕ) :
    responseCoefficient (0 : ℕ → ℂ) b n = 0 := by
  cases b <;> cases n <;>
    simp [responseCoefficient_even_zero, responseCoefficient_even_succ, responseCoefficient_odd]

theorem directionalBudget_zero_left (d : ℕ → ℂ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    directionalBudget 0 d b r x y = 0 := by
  simp [directionalBudget, coefficientBudget, responseCoefficient_zero]

theorem directionalBudget_zero_right (d : ℕ → ℂ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    directionalBudget d 0 b r x y = 0 := by
  simp [directionalBudget, coefficientBudget]

/-- Proven from original C3 tails and completion, for each fixed finite direction.
No pivot sign, positive prefix, or uniform coercivity assumption is used. -/
theorem literal_error_budget_tendsto_zero (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    Tendsto (fun M => literalErrorBudget M M b r x y) atTop (nhds 0) := by
  have hHT := directionalBudget_tendsto literalHead literalTail (fun n => (nativeC n:ℂ)) 0
    literal_head_tendsto literal_tail_tendsto_zero b r x y
  have hTH := directionalBudget_tendsto literalTail literalHead 0 (fun n => (nativeC n:ℂ))
    literal_tail_tendsto_zero literal_head_tendsto b r x y
  have hTT := directionalBudget_tendsto literalTail literalTail 0 0
    literal_tail_tendsto_zero literal_tail_tendsto_zero b r x y
  simpa [literalErrorBudget, directionalBudget_zero_left, directionalBudget_zero_right] using
    (hHT.add hTH).add hTT

end
end CarrySourceBezout
