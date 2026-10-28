import CoercivePhysicalMargin
namespace CarryCriticalComplete
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- The existing boundary chart of the actual completed physical coefficient. -/
def sourceBoundary (k : ℕ) (x : ℕ →₀ ℂ) : Fin 4 → ℂ :=
  radialFourScaledBoundary (radialFourSourceStep k) (physicalValues k 4 x)

def criticalBoundary (a : ℝ) (k : ℕ) : Fin 4 → ℂ := sourceBoundary k (criticalOddSource a k)
def defectBoundary (a : ℝ) (k : ℕ) : Fin 4 → ℂ := sourceBoundary k (defectInput a k)

/-- This coordinate calculation is linear even before regularity is used. -/
theorem physical_values_sub (k N : ℕ) (x y : ℕ →₀ ℂ) :
    physicalValues k N (x-y)=physicalValues k N x-physicalValues k N y := by
  funext i
  simp only [physicalValues,physicalCoefficients,radialCompletedValueCoefficients,
    Finsupp.sub_apply,Pi.sub_apply]
  ring

theorem source_boundary_sub (k : ℕ) (x y : ℕ →₀ ℂ) :
    sourceBoundary k (x-y)=sourceBoundary k x-sourceBoundary k y := by
  unfold sourceBoundary
  rw [physical_values_sub]
  funext i
  simp only [radialFourScaledBoundary,radialEulerBoundaryJet,Pi.sub_apply,
    sub_mul,Finset.sum_sub_distrib,mul_sub]

theorem physical_values_smul (k N : ℕ) (z : ℂ) (x : ℕ →₀ ℂ) :
    physicalValues k N (z • x)=z • physicalValues k N x := by
  funext i
  simp only [physicalValues,physicalCoefficients,radialCompletedValueCoefficients,
    Finsupp.smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem source_boundary_smul (k : ℕ) (z : ℂ) (x : ℕ →₀ ℂ) :
    sourceBoundary k (z • x)=z • sourceBoundary k x := by
  unfold sourceBoundary
  rw [physical_values_smul]
  funext i
  simp only [radialFourScaledBoundary,radialEulerBoundaryJet,Pi.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Same complete source decomposition, now in all four boundary coordinates. -/
theorem critical_boundary_split (a : ℝ) (k : ℕ) :
    criticalBoundary a k=principalBoundary a k-defectBoundary a k := by
  change sourceBoundary k (criticalOddSource a k)=sourceBoundary k (principalInput a k)-sourceBoundary k (defectInput a k)
  rw [critical_input_split,source_boundary_sub]

theorem critical_four_support (a : ℝ) (k : ℕ) :
    (criticalOddSource a k).support ⊆ Finset.range 4 := by
  rw [critical_input_split]
  exact Finsupp.support_sub.trans (Finset.union_subset (principal_support a k) (defect_support a k))

/-- Literal correction coefficients, including their original imaginary phase. -/
theorem defect_coefficient_formula (a : ℝ) (k : ℕ) (i : Fin 4) :
    defectInput a k i=Complex.I*((7*a*((k:ℝ)+1)/6 * ![-1,6,-9,4] i:ℝ):ℂ) := by
  fin_cases i <;> norm_num [defectInput,Finsupp.smul_apply,smul_eq_mul,
    address_power_apply,native_odd_coefficient,nativeOddBeta] <;> ring

/-- Original full critical coefficients; the correction is subtracted exactly. -/
theorem critical_coefficient_formula (a : ℝ) (k : ℕ) (i : Fin 4) :
    criticalOddSource a k i=Complex.I*((((k:ℝ)+1)/6 *
      ![-(((k:ℝ)+1)^2)-6*a,3*((k:ℝ)+1)^2+6*a,-(3*((k:ℝ)+1)^2),((k:ℝ)+1)^2] i:ℝ):ℂ) := by
  rw [critical_input_split]
  simp only [Finsupp.sub_apply,principal_coefficient_formula,defect_coefficient_formula]
  fin_cases i <;> norm_num <;> ring

def criticalTemplate (a t : ℝ) : Fin 4 → ℂ :=
  fun i => Complex.I*((![0,a,3*a*t,1+7*a*t^2] i/Real.sqrt 2:ℝ):ℂ)

def defectTemplate (a t : ℝ) : Fin 4 → ℂ :=
  fun i => Complex.I*((![0,0,7*a*t,70*a*t^2] i/Real.sqrt 2:ℝ):ℂ)

theorem critical_boundary_exact (a : ℝ) (k : ℕ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    criticalBoundary a k=criticalTemplate a (radialFourSourceStep k) := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [criticalBoundary,sourceBoundary,physical_values_eq k 4 (criticalOddSource a k) hF hP]
  funext i
  fin_cases i <;> norm_num [radialFourScaledBoundary,radialEulerBoundaryJet,critical_coefficient_formula,
    Fin.sum_univ_succ,radialFourSourceStep,criticalTemplate] <;> field_simp [hk,hs] <;> ring

theorem defect_boundary_exact (a : ℝ) (k : ℕ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    defectBoundary a k=defectTemplate a (radialFourSourceStep k) := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [defectBoundary,sourceBoundary,physical_values_eq k 4 (defectInput a k) hF hP]
  funext i
  fin_cases i <;> norm_num [radialFourScaledBoundary,radialEulerBoundaryJet,defect_coefficient_formula,
    Fin.sum_univ_succ,radialFourSourceStep,defectTemplate] <;> field_simp [hk,hs] <;> ring
  simp

/-- ONE regular prefix threshold, independent of all real parameters. -/
theorem boundary_eventually_exact :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      criticalBoundary a k=criticalTemplate a (radialFourSourceStep k) ∧
      defectBoundary a k=defectTemplate a (radialFourSourceStep k) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  intro a
  exact ⟨critical_boundary_exact a k (fun i => (hk i).2.1) (fun i => (hk i).2.2),
    defect_boundary_exact a k (fun i => (hk i).2.1) (fun i => (hk i).2.2)⟩

theorem critical_boundary_tendsto (a : ℝ) :
    Tendsto (criticalBoundary a) atTop (nhds (boundaryLimit a)) := by
  have hc : Continuous (criticalTemplate a) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [criticalTemplate] <;> fun_prop
  have ht := hc.continuousAt.tendsto.comp radialFourSourceStep_tendsto_zero
  have he : criticalTemplate a 0=boundaryLimit a := by
    funext i
    fin_cases i <;> simp [criticalTemplate,boundaryLimit,boundaryTemplate]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [boundary_eventually_exact] with k hk
  exact (hk a).1.symm

theorem defect_boundary_tendsto_zero (a : ℝ) :
    Tendsto (defectBoundary a) atTop (nhds 0) := by
  have hc : Continuous (defectTemplate a) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [defectTemplate] <;> fun_prop
  have ht := hc.continuousAt.tendsto.comp radialFourSourceStep_tendsto_zero
  have he : defectTemplate a 0=0 := by
    funext i
    fin_cases i <;> simp [defectTemplate]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [boundary_eventually_exact] with k hk
  exact (hk a).2.symm

theorem critical_template_norm_sq (a t : ℝ) :
    (∑ i : Fin 4, Complex.normSq (criticalTemplate a t i))=
      (a^2+(3*a*t)^2+(1+7*a*t^2)^2)/2 := by
  have hs : (Real.sqrt 2)⁻¹^2=(1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  norm_num [criticalTemplate,Fin.sum_univ_succ,Complex.normSq_apply]
  ring_nf
  simp only [hs]
  ring

theorem critical_boundary_uniform_lower :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      (a^2+1)/4 ≤ ∑ i : Fin 4, Complex.normSq (criticalBoundary a k i) := by
  have ht : Tendsto (fun k : ℕ => (7*(radialFourSourceStep k)^2)^2) atTop (nhds (0:ℝ)) := by
    simpa using ((radialFourSourceStep_tendsto_zero.pow 2).const_mul 7).pow 2
  have hs := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hs,boundary_eventually_exact] with k hk he
  intro a
  rw [(he a).1,critical_template_norm_sq]
  have hb := boundary_shear_lower a (7*(radialFourSourceStep k)^2) hk.le
  nlinarith [sq_nonneg (3*a*radialFourSourceStep k)]

end
end CarryCriticalComplete
