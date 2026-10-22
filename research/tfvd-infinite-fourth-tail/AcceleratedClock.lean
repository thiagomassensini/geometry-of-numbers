import InfiniteOrdinary

/-! The original log-clock channel, with the same finite TFVD endpoint.
The factor i(m+1) is proved for normalized jets, not inserted by matching. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def nativeClockBoundary (a : ℕ) (t : ℝ) : ℂ :=
  tailBoundary (fun n => (Real.log (n:ℝ):ℂ)*criticalMaterialSample t n) a

theorem boundary_hasDerivAt_clock (a : ℕ) (t : ℝ) :
    HasDerivAt (nativeBoundary a) (-Complex.I*nativeClockBoundary a t) t := by
  have h := ((((criticalMaterialSample_hasDerivAt t (a+2)).const_mul 3).sub
    ((criticalMaterialSample_hasDerivAt t (a+1)).const_mul 8)).add
    ((criticalMaterialSample_hasDerivAt t a).const_mul 5)).div_const 8
  change HasDerivAt (nativeBoundary a) _ t at h
  convert h using 1
  unfold nativeClockBoundary tailBoundary
  ring

theorem boundary_clock_derivative (a : ℕ) :
    nativeClockBoundary a = fun t => Complex.I*deriv (nativeBoundary a) t := by
  funext t
  rw [(boundary_hasDerivAt_clock a t).deriv, ← mul_assoc, mul_neg, Complex.I_mul_I]
  simp

theorem native_clock_boundary_analytic (a : ℕ) (ha : 0 < a) :
    AnalyticAt ℝ (nativeClockBoundary a) 0 := by
  rw [boundary_clock_derivative]
  exact (analyticAt_const (v:=(Complex.I:ℂ))).mul (native_boundary_analytic a ha).deriv

theorem boundary_clock_jet (m a : ℕ) (ha : 0 < a) :
    rJet m (nativeClockBoundary a) = Complex.I*(m+1:ℕ)*boundaryJet (m+1) a := by
  rw [boundary_clock_derivative]
  rw [rJet_derivative (f:=fun t => Complex.I*deriv (nativeBoundary a) t)
    ((analyticAt_const (v:=(Complex.I:ℂ))).mul (native_boundary_analytic a ha).deriv)]
  unfold boundaryJet
  rw [rJet_derivative (native_boundary_analytic a ha), iteratedDeriv_const_mul_field,
    ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem return_clock_jet (m : ℕ) :
    rJet m carryValveKappa = Complex.I*(m+1:ℕ)*rJet (m+1) baseTwoCompletedBoundaryValue := by
  unfold rJet
  rw [clock_return_jet_cells, return_jet_cells]
  simp_rw [clock_jet_coefficient, ← cell_jet_coefficient]
  rw [tsum_mul_left]

theorem finite_clock_jet (m M : ℕ) :
    rJet m (clockHead M) = Complex.I*(m+1:ℕ)*rJet (m+1) (ordinaryHead M) := by
  unfold clockHead ordinaryHead
  rw [rJet_sum _ _ (fun k _ => clock_cell_real_analytic k),
    rJet_sum _ _ (fun k _ => cell_real_analytic k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : rJet m (clockCell k) = clockCellJet m k := by
    change carryScalarJetShift m ((cellJetCoordinate k).restrictScalars ℝ ∘ baseTwoCompletedMaterialClockL1) 0 = _
    rw [map_l1_jets _ (material_clock_l1_analytic 0)]
    rfl
  rw [he, clock_jet_coefficient, ← cell_jet_coefficient, rJet, ← cell_jet_source]

def acceleratedClockHead (M : ℕ) (t : ℝ) : ℂ :=
  clockHead M t+nativeClockBoundary (4*M+3) t

def acceleratedClockTail (M : ℕ) (t : ℝ) : ℂ :=
  carryValveKappa t-acceleratedClockHead M t

theorem accelerated_clock_head_analytic (M : ℕ) : AnalyticAt ℝ (acceleratedClockHead M) 0 :=
  (clock_head_analytic M).add (native_clock_boundary_analytic _ (by omega))

theorem accelerated_clock_tail_analytic (M : ℕ) : AnalyticAt ℝ (acceleratedClockTail M) 0 :=
  kappa_real_analytic.sub (accelerated_clock_head_analytic M)

/-- The second channel has the SAME controlled remainder, with one higher
jet order. No powers of an unbounded material operator are assumed. -/
theorem accelerated_clock_jet_exact (m M : ℕ) :
    rJet m (acceleratedClockTail M) =
      Complex.I*(m+1:ℕ)*rJet (m+1) (acceleratedOrdinaryTail M) := by
  unfold acceleratedClockTail acceleratedOrdinaryTail
  rw [rJet_sub kappa_real_analytic (accelerated_clock_head_analytic M),
    rJet_sub beta_real_analytic (accelerated_ordinary_head_analytic M)]
  unfold acceleratedClockHead acceleratedOrdinaryHead
  rw [rJet_add (clock_head_analytic M) (native_clock_boundary_analytic _ (by omega)),
    rJet_add (ordinary_head_analytic M) (native_boundary_analytic _ (by omega)),
    return_clock_jet, finite_clock_jet, boundary_clock_jet m _ (by omega)]
  change _-(_+_) = Complex.I*(m+1:ℕ)*(_-(_+boundaryJet (m+1) (4*M+3)))
  ring

theorem accelerated_clock_jet_series (m M : ℕ) :
    rJet m (acceleratedClockTail M) = Complex.I*(m+1:ℕ)*
      ∑' k, remainderJet (m+1) (4*(k+M)+3) := by
  rw [accelerated_clock_jet_exact, accelerated_ordinary_jet_exact]

def acceleratedClockBudget (m M : ℕ) : ℝ :=
  (m+1:ℕ)*30*2^(m+1)/(12*(4*(M:ℝ)-1)^3)

theorem accelerated_clock_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (acceleratedClockTail M)‖ ≤ acceleratedClockBudget m M := by
  rw [accelerated_clock_jet_exact, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left (accelerated_ordinary_jet_bound (m+1) M hM)
    (by positivity : (0:ℝ) ≤ (m+1:ℕ))
  simpa only [acceleratedClockBudget, acceleratedOrdinaryBudget, mul_div_assoc, mul_assoc] using h
end
end CarryFourthTail
