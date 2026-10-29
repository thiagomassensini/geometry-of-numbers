import SourceReadouts

/-! Exact mixed-radial defect. Radial indices are regularization labels,
not cameras or carry depths. No reweighting of a cross is performed. -/
namespace CarryCompletedTrace
open CarrySelfAdjointOperator
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

def radialMass (k : ℕ) : ℝ := (k : ℝ)+1
def radialCrossGram (k l i j : ℕ) : ℂ :=
  inner ℂ (completedNativeRadialChiralCauchyState k i)
    (completedNativeRadialChiralCauchyState l j)
def crossRadialFactor (k l i j : ℕ) : ℝ :=
  Real.sqrt (radialMass k)*Real.sqrt (radialMass l) /
    ((i : ℝ)+j+2) * (((i : ℝ)+1)/radialMass k + ((j : ℝ)+1)/radialMass l)
def crossRadialDefect (k l i j : ℕ) : ℂ :=
  radialCrossGram k l i j *
    (1-conj (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i))*
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint l j))

theorem radial_cross_gram (k l i j : ℕ) :
    radialCrossGram k l i j =
      ((Real.sqrt (radialMass k)*Real.sqrt (radialMass l) / ((i : ℝ)+j+2) : ℝ) : ℂ) := by
  unfold radialCrossGram completedNativeRadialChiralCauchyState radialMass
  rw [inner_smul_left,inner_smul_right,inner_completedNativeChiralCauchyFeature]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem mixed_radial_separation (k l i j : ℕ) :
    canonicalCompletedC3RadialTiltPoint l j-conj (canonicalCompletedC3RadialTiltPoint k i) =
      Complex.I * ((((i : ℝ)+1)/radialMass k + ((j : ℝ)+1)/radialMass l : ℝ) : ℂ) := by
  rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im l j,
    canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k i]
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,
    canonicalCompletedC3RadialTiltPoint_im,radialMass,div_eq_mul_inv]
  push_cast
  ring

theorem mixed_radial_separation_ne (k l i j : ℕ) :
    canonicalCompletedC3RadialTiltPoint l j ≠ conj (canonicalCompletedC3RadialTiltPoint k i) := by
  apply sub_ne_zero.mp
  rw [mixed_radial_separation]
  apply mul_ne_zero Complex.I_ne_zero
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold radialMass; positivity))

theorem cross_factor_pos (k l i j : ℕ) : 0 < crossRadialFactor k l i j := by
  unfold crossRadialFactor radialMass
  positivity

theorem radial_cross_gram_eq_factor (k l i j : ℕ) :
    radialCrossGram k l i j = (crossRadialFactor k l i j : ℂ)*Complex.I /
      (canonicalCompletedC3RadialTiltPoint l j-conj (canonicalCompletedC3RadialTiltPoint k i)) := by
  rw [radial_cross_gram,mixed_radial_separation]
  have hs : ((((i : ℝ)+1)/radialMass k + ((j : ℝ)+1)/radialMass l : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold radialMass; positivity))
  unfold crossRadialFactor
  push_cast at hs ⊢
  field_simp [Complex.I_ne_zero,hs]

/-- The familiar equality with Pick is exact only after retaining this
mixed-radial geometric factor. It is not silently declared one. -/
theorem cross_defect_eq_factor_pick (k l i j : ℕ) :
    crossRadialDefect k l i j = (crossRadialFactor k l i j : ℂ)*
      completedNativeHermiteBiehlerChiralPickKernel
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  rw [crossRadialDefect,radial_cross_gram_eq_factor]
  unfold completedNativeHermiteBiehlerChiralPickKernel
  ring

theorem cross_defect_is_original_pairing (k l i j : ℕ) :
    crossRadialDefect k l i j =
      inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState l j) -
      inner ℂ (completedNativeRadialChiralMultiplierState k i) (completedNativeRadialChiralMultiplierState l j) := by
  unfold crossRadialDefect radialCrossGram completedNativeRadialChiralMultiplierState
  rw [inner_smul_left,inner_smul_right]
  ring

/-- Exact correction to the canonical kernel; not a positivity hypothesis. -/
theorem native_kernel_cross_factor (k l i j : ℕ)
    (hz : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l j) ≠ 0)
    (hzP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l j) ≠ 0) :
    completedNativeNormalizedPositiveChiralTraceKernel
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) *
      crossRadialDefect k l i j =
    (crossRadialFactor k l i j : ℂ) * canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  rw [cross_defect_eq_factor_pick,
    canonicalCompletedNativePolarizedDslopeKernel_eq_positive_mul_pick hz hzF hwF
      (mixed_radial_separation_ne k l i j) hzP hwP]
  ring

theorem cross_factor_same_radial (k i j : ℕ) : crossRadialFactor k k i j = 1 := by
  unfold crossRadialFactor
  rw [← pow_two,Real.sq_sqrt (by unfold radialMass; positivity)]
  have hk : radialMass k ≠ 0 := by unfold radialMass; positivity
  have hn : (i : ℝ)+j+2 ≠ 0 := by positivity
  field_simp
  ring

theorem doubled_radial_mass (k : ℕ) : radialMass (2*k+1) = 2*radialMass k := by
  unfold radialMass
  push_cast
  ring

theorem doubled_radial_sqrt_product (k : ℕ) :
    Real.sqrt (radialMass k)*Real.sqrt (radialMass (2*k+1)) = Real.sqrt 2*radialMass k := by
  rw [doubled_radial_mass,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = Real.sqrt 2 * (Real.sqrt (radialMass k))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by unfold radialMass; positivity)]

/-- Same spectral argument, distinct original material addresses. -/
theorem doubled_radial_same_point (k : ℕ) :
    canonicalCompletedC3RadialTiltPoint (2*k+1) 1 = canonicalCompletedC3RadialTiltPoint k 0 := by
  apply Complex.ext
  · simp [canonicalCompletedC3RadialTiltPoint,canonicalCompletedC3RadialTiltStep,canonicalGreenJetStep]
  · rw [canonicalCompletedC3RadialTiltPoint_im,canonicalCompletedC3RadialTiltPoint_im]
    have hk : (k : ℝ)+1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem cross_factor_same_point (k : ℕ) :
    crossRadialFactor k (2*k+1) 0 1 = 2*Real.sqrt 2/3 := by
  unfold crossRadialFactor
  rw [doubled_radial_sqrt_product,doubled_radial_mass]
  have hk : radialMass k ≠ 0 := by unfold radialMass; positivity
  norm_num
  field_simp
  ring

theorem same_point_factor_lt_one : 2*Real.sqrt 2/3 < 1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h' := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem radial_column_norm_sq (k i : ℕ) :
    ‖completedNativeRadialChiralCauchyState k i‖^2 =
      radialMass k / ((i : ℝ)+i+2) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_completedNativeRadialChiralCauchyState]
  unfold radialMass
  norm_cast

theorem same_parameter_state_difference_norm_sq (k : ℕ) :
    ‖completedNativeRadialChiralCauchyState k 0 -
      completedNativeRadialChiralCauchyState (2*k+1) 1‖^2 =
      radialMass k*(1-2*Real.sqrt 2/3) := by
  have hc : inner ℂ (completedNativeRadialChiralCauchyState k 0)
      (completedNativeRadialChiralCauchyState (2*k+1) 1) =
        ((Real.sqrt 2 * radialMass k / 3 : ℝ) : ℂ) := by
    change radialCrossGram k (2*k+1) 0 1 = _
    rw [radial_cross_gram,doubled_radial_sqrt_product]
    norm_num
  rw [@norm_sub_sq ℂ,radial_column_norm_sq,radial_column_norm_sq,hc,
    doubled_radial_mass]
  norm_num
  ring

/-- Equality of the scalar spectral argument is NOT physical redundancy. -/
theorem same_parameter_states_ne (k : ℕ) :
    completedNativeRadialChiralCauchyState k 0 ≠
      completedNativeRadialChiralCauchyState (2*k+1) 1 := by
  intro he
  have hn := same_parameter_state_difference_norm_sq k
  rw [he,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at hn
  have hp : 0 < radialMass k*(1-2*Real.sqrt 2/3) :=
    mul_pos (by unfold radialMass; positivity) (sub_pos.mpr same_point_factor_lt_one)
  linarith

theorem same_parameter_return_difference (k : ℕ) :
    completedNativeRadialChiralMultiplierState k 0 -
      completedNativeRadialChiralMultiplierState (2*k+1) 1 =
    completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k 0) •
      (completedNativeRadialChiralCauchyState k 0 -
        completedNativeRadialChiralCauchyState (2*k+1) 1) := by
  rw [completedNativeRadialChiralMultiplierState,completedNativeRadialChiralMultiplierState,
    doubled_radial_same_point,smul_sub]

/-- Literal residual, including its factor, rather than an unnamed equality gate. -/
theorem cross_defect_same_point_residual (k : ℕ) :
    crossRadialDefect k (2*k+1) 0 1 -
      completedNativeHermiteBiehlerChiralPickKernel
        (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint k 0) =
    ((2*Real.sqrt 2/3-1 : ℝ) : ℂ)*
      completedNativeHermiteBiehlerChiralPickKernel
        (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint k 0) := by
  rw [cross_defect_eq_factor_pick,cross_factor_same_point,doubled_radial_same_point]
  push_cast
  ring

end
end CarryCompletedTrace
