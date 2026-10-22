import JetTails

namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000

def clockCell (k : ℕ) (t : ℝ) : ℂ :=
  cellJetCoordinate k (baseTwoCompletedMaterialClockL1 t)

theorem clock_cell_real_derivative (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u => baseTwoCriticalCenterCell u k) (-Complex.I * clockCell k t) t := by
  have h := ((cellJetCoordinate k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradient_hasDerivAt_clock t)
  have he : (fun u => baseTwoCriticalCenterCell u k) =
      (cellJetCoordinate k).restrictScalars ℝ ∘ baseTwoCompletedMaterialGradient := by
    funext u
    rw [baseTwoCriticalCenterCell_eq_gradientEdges]
    rfl
  rw [he]
  change HasDerivAt _ ((cellJetCoordinate k) (-Complex.I • baseTwoCompletedMaterialClockL1 t)) t at h
  simpa only [map_smul, smul_eq_mul, clockCell] using h

theorem complex_clock_real (k : ℕ) (t : ℝ) :
    Complex.I * deriv (complexCell k) (t:ℂ) = clockCell k t := by
  have hc := ((complex_cell_entire k (t:ℂ)).hasDerivAt.comp_ofReal)
  have he : (fun u : ℝ => complexCell k (u:ℂ)) = fun u => baseTwoCriticalCenterCell u k :=
    funext (complex_cell_real k)
  rw [he] at hc
  rw [hc.unique (clock_cell_real_derivative k t)]
  rw [← mul_assoc, mul_neg, Complex.I_mul_I]
  simp

theorem complex_jet_derivative (f : ℂ → ℂ) (m : ℕ) :
    complexJet m (fun z => Complex.I * deriv f z) =
      Complex.I * (m+1:ℕ) * complexJet (m+1) f := by
  simp only [complexJet, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem clock_jet_coefficient (m k : ℕ) :
    clockCellJet m k = Complex.I * (m+1:ℕ) * complexJet (m+1) (complexCell k) := by
  have he : clockCellJet m k = carryScalarJetShift m (clockCell k) 0 := by
    have hcomp : clockCell k = (cellJetCoordinate k).restrictScalars ℝ ∘
        baseTwoCompletedMaterialClockL1 := rfl
    rw [hcomp, map_l1_jets _ (material_clock_l1_analytic 0)]
    rfl
  rw [he, real_jet_complex (.of_forall (fun t => (complex_clock_real k t).symm))
    ((analyticAt_const (v:=(Complex.I:ℂ))).mul ((complex_cell_entire k).analyticAt 0).deriv)]
  exact complex_jet_derivative _ m

theorem clock_cell_jet_bound (m k : ℕ) :
    ‖clockCellJet m k‖ ≤ (m+1:ℕ)*2^(m+2) / ((4*k+3:ℕ):ℝ)^2 := by
  rw [clock_jet_coefficient, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
  simpa only [Nat.add_assoc, mul_div_assoc] using
    mul_le_mul_of_nonneg_left (complex_jet_bound (m+1) k) (by positivity : (0:ℝ) ≤ (m+1:ℕ))

theorem clock_return_jet_quantitative (m M : ℕ) (hM : 0 < M) :
    ‖carryScalarJetShift m carryValveKappa 0-
      (∑ k ∈ Finset.range M, clockCellJet m k)‖ ≤
        (m+1:ℕ)*2^(m+2)/(4*(4*(M:ℝ)-1)) := by
  apply (clock_return_jet_tail_bound m M).trans
  have hs : Summable (fun k : ℕ => (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
      (by intro i j h; dsimp at h; omega)
  calc
    ∑' k, ‖clockCellJet m (k+M)‖ ≤ ∑' k,
        ((m+1:ℕ):ℝ)*2^(m+2)*((1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
      (clock_cell_jet_norm_summable m |>.comp_injective (by intro i j h; exact Nat.add_right_cancel h)).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using clock_cell_jet_bound m (k+M)) (hs.mul_left _)
    _ = ((m+1:ℕ):ℝ)*2^(m+2)*(∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) := tsum_mul_left
    _ ≤ (m+1:ℕ)*2^(m+2)/(4*(4*(M:ℝ)-1)) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (reciprocal_cell_tail M hM)
        (by positivity : (0:ℝ) ≤ ((m+1:ℕ):ℝ)*2^(m+2))
end
end CarryCellTail
