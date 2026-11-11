import KernelBudget
import SourceMap

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem responseCoefficient_even (c : ℕ → ℂ) (n : ℕ) :
    responseCoefficient c false n = -(n : ℂ) * c n := by
  cases n with
  | zero => simp [responseCoefficient, sourceResponse, sourceSeries]
  | succ n =>
      simp [responseCoefficient, sourceResponse, sourceSeries,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      have hcast : -((↑n : ℂ) + 1) = (-1 : ℂ) + -↑n := by abel
      calc
        -(c (n+1) * (↑n + 1)) = -((↑n + 1) * c (n+1)) := by
          congr 1
          exact mul_comm _ _
        _ = (-(↑n + 1)) * c (n+1) := by rw [← neg_mul]
        _ = (-1 + -↑n) * c (n+1) := by rw [hcast]

theorem responseCoefficient_odd (c : ℕ → ℂ) (n : ℕ) :
    responseCoefficient c true n = -((n+1 : ℕ) : ℂ) * c (n+1) := by
  simp [responseCoefficient, sourceResponse, sourceSeries,
    PowerSeries.coeff_derivative]
  ring

/-- Explicit ordinary-sector entries, obtained from the existing mixed-kernel
coefficient formula by specializing its two sources to the same sequence. -/
theorem sourceKernel_even_coefficient_explicit (c : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c false)) =
      ∑ k ∈ Finset.range (j+1),
        ((j : ℝ) - i - 2*k - 1) * c (j-k) * c (i+k+1) := by
  let cℂ : ℕ → ℂ := fun n => (c n : ℂ)
  have hmix := mixed_kernel_coefficient cℂ cℂ false i j
  have hmap := sourceKernel_map Complex.ofRealHom c false
  have hcoeff := congrArg (fun f : BiSeries ℂ => PowerSeries.coeff j (PowerSeries.coeff i f)) hmap
  simp only [mapBi, PowerSeries.coeff_map] at hcoeff
  have hreal : ((PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c false)) : ℝ) : ℂ) =
      PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel cℂ false)) := by
    simpa [cℂ] using hcoeff.symm
  apply Complex.ofReal_injective
  rw [hreal]
  change PowerSeries.coeff j (PowerSeries.coeff i
    (mixedSourceKernel cℂ cℂ false)) = _
  rw [hmix]
  simp_rw [responseCoefficient_even]
  simp only [cℂ]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by simpa using hk
  rw [Nat.cast_sub hkj]
  ring

/-- Explicit shifted-sector entries, from the same mixed-kernel formula. -/
theorem sourceKernel_odd_coefficient_explicit (c : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c true)) =
      ∑ k ∈ Finset.range (j+1),
        (((j-k+1 : ℕ) : ℝ) * c (j-k+1) * c (i+k+1) -
          ((i+k+2 : ℕ) : ℝ) * c (j-k) * c (i+k+2)) := by
  let cℂ : ℕ → ℂ := fun n => (c n : ℂ)
  have hmix := mixed_kernel_coefficient cℂ cℂ true i j
  have hmap := sourceKernel_map Complex.ofRealHom c true
  have hcoeff := congrArg (fun f : BiSeries ℂ => PowerSeries.coeff j (PowerSeries.coeff i f)) hmap
  simp only [mapBi, PowerSeries.coeff_map] at hcoeff
  have hreal : ((PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c true)) : ℝ) : ℂ) =
      PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel cℂ true)) := by
    simpa [cℂ] using hcoeff.symm
  apply Complex.ofReal_injective
  rw [hreal]
  change PowerSeries.coeff j (PowerSeries.coeff i
    (mixedSourceKernel cℂ cℂ true)) = _
  rw [hmix]
  simp_rw [responseCoefficient_odd]
  simp only [cℂ]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by simpa using hk
  rw [Nat.cast_sub hkj]
  ring

/-- An entry in either source kernel only reads the coefficient prefix through
`i+j+s+1`, with `s=0` in the ordinary sector and `s=1` in the shifted sector. -/
theorem sourceKernel_coefficient_depends_on_prefix
    (c d : ℕ → ℝ) (b : Bool) (i j : ℕ)
    (hprefix : ∀ r, r ≤ i+j+(if b then 2 else 1) → c r = d r) :
    PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c b)) =
      PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel d b)) := by
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hprefix
      rw [sourceKernel_even_coefficient_explicit, sourceKernel_even_coefficient_explicit]
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≤ j := by simpa using hk
      rw [hprefix (j-k) (by omega), hprefix (i+k+1) (by omega)]
  | true =>
      simp only [if_true] at hprefix
      rw [sourceKernel_odd_coefficient_explicit, sourceKernel_odd_coefficient_explicit]
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≤ j := by simpa using hk
      rw [hprefix (j-k+1) (by omega), hprefix (i+k+1) (by omega),
        hprefix (j-k) (by omega), hprefix (i+k+2) (by omega)]

#print axioms responseCoefficient_even
#print axioms responseCoefficient_odd
#print axioms sourceKernel_even_coefficient_explicit
#print axioms sourceKernel_odd_coefficient_explicit
#print axioms sourceKernel_coefficient_depends_on_prefix

end
end CarrySourceBezout
