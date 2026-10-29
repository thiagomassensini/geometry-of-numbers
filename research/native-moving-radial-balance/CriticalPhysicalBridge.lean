import CurveRegularity
import CriticalOddTaylor

namespace CarryMovingRadial
open CarrySelfAdjointOperator CarrySelfAdjointOperator.PhysicalSewing NativeLaguerre
open scoped BigOperators ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def criticalRaw (a : ℝ) (z : ℂ) : Fin 4 → ℂ := fun i =>
  Complex.I/(6*z^3)*criticalWeight a z i

theorem critical_raw_at_grid (a : ℝ) (k : ℕ) (i : Fin 4) :
    criticalRaw a (canonicalGreenJetStep k) i=CarryCubicOdd.criticalOddSource a k i := by
  rw [CarryCriticalComplete.critical_coefficient_formula]
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  fin_cases i <;> norm_num [criticalRaw,criticalWeight,canonicalGreenJetStep] <;>
    field_simp [hk]

theorem finite_coefficients_restrict (N : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support⊆Finset.range N) : finRadialCoefficients N (fun i => x i)=x := by
  ext j
  by_cases hj : j<N
  · exact finRadialCoefficients_apply N _ ⟨j,hj⟩
  · rw [finRadialCoefficients_outside N _ j (by omega)]
    have hz : x j=0 := Finsupp.notMem_support_iff.mp (fun hm =>
      (not_lt_of_ge (Nat.le_of_not_lt hj)) (Finset.mem_range.mp (hx hm)))
    exact hz.symm

theorem critical_curve_eq_original (a : ℝ) (k : ℕ) :
    curveState 4 (radialFourSourceStep k) (criticalRaw a (canonicalGreenJetStep k))=
      physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource a k) := by
  rw [curve_eq_original]
  have he : criticalRaw a (canonicalGreenJetStep k)=fun i : Fin 4 => CarryCubicOdd.criticalOddSource a k i := by
    funext i; exact critical_raw_at_grid a k i
  rw [he,finite_coefficients_restrict 4 _ (CarryCriticalComplete.critical_four_support a k)]

/-- Actual critical input regularity, not an abstract differentiability gate. -/
theorem critical_raw_differentiable (a t : ℝ) (ht : 0<t) (i : Fin 4) :
    DifferentiableAt ℝ (fun h : ℝ => criticalRaw a (h:ℂ) i) t := by
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hd : (6:ℂ)*(t:ℂ)^3≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hn)
  have ha : AnalyticAt ℂ (fun z => criticalRaw a z i) (t:ℂ) := by
    fin_cases i <;> dsimp [criticalRaw,criticalWeight] <;> fun_prop (disch := assumption)
  exact ha.differentiableAt.hasDerivAt.comp_ofReal.differentiableAt

theorem curve_regular_eventually (N : ℕ) :
    ∀ᶠ h : ℝ in nhds 0, ∀ i : Fin N,
      point h i∈completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic (point h i)≠0 ∧
        completedNativePositiveHermiteBiehlerCoordinate (point h i)≠0 := by
  apply Filter.eventually_all.mpr
  intro i
  have ht : Tendsto (fun h : ℝ => point h i) (nhds 0) (nhds 0) := by
    simpa only [point,Complex.ofReal_zero,mul_zero] using
      (Complex.continuous_ofReal.tendsto (0:ℝ)).const_mul (Complex.I*((i:ℂ)+1))
  exact ht.eventually completedNativeChiralPickFactorization_eventually_regular

/-- Every source-side gate of the moving derivative is discharged near the
center for the ORIGINAL critical family. The coefficients remain free of moments. -/
theorem critical_physical_derivative (a : ℝ) :
    ∀ᶠ t : ℝ in nhds 0, 0<t →
      deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
        (curveState 4 h (criticalRaw a (h:ℂ))) (curveState 4 h (criticalRaw a (h:ℂ)))) t=
        fullPair 4 (fun i => curveQuotient t i)
          (coefficientVelocity 4 (fun h => criticalRaw a (h:ℂ)) t)
          (curveCoefficients 4 t (criticalRaw a (t:ℂ)))+
        fullPair 4 (fun i => curveQuotient t i)
          (curveCoefficients 4 t (criticalRaw a (t:ℂ)))
          (coefficientVelocity 4 (fun h => criticalRaw a (h:ℂ)) t)+
        returnVariation 4 (fun i => curveQuotient t i) (returnVelocity 4 t)
          (curveCoefficients 4 t (criticalRaw a (t:ℂ)))
          (curveCoefficients 4 t (criticalRaw a (t:ℂ))) := by
  filter_upwards [curve_regular_eventually 4] with t ht hp
  exact physical_moving_derivative 4 (fun h => criticalRaw a (h:ℂ)) t hp
    (critical_raw_differentiable a t hp) (fun i => (ht i).1)
    (fun i => (ht i).2.1) (fun i => (ht i).2.2)

end
end CarryMovingRadial
