import EndpointCore

/-! Literal power pullback on the ORIGINAL physical half-density columns.
The natural number m denotes the power m+1, never a carry depth or camera.
No moment, source sign or fitted inverse is used. -/
namespace CarryRadialRefinement
open CarryPhysicalTrace CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

def refinedAddress (m j : ℕ) : ℕ := (m+1)*j+m

theorem refined_address_succ (m j : ℕ) : refinedAddress m j+1 = (m+1)*(j+1) := by
  unfold refinedAddress
  ring

def powerColumn (m j : ℕ) : PhysicalCauchySpace :=
  (Real.sqrt ((m : ℝ)+1) : ℂ) • physicalCauchyFeature (refinedAddress m j)

/-- The Jacobian square root is forced by x ↦ x^(m+1). -/
theorem power_column_function (m j : ℕ) (x : unitInterval) :
    (Real.sqrt ((m : ℝ)+1) : ℂ) *
      completedNativeChiralCauchyContinuousFeature (refinedAddress m j) x =
    ((Real.sqrt (((m : ℝ)+1)*(x : ℝ)^m) : ℝ) : ℂ) *
      completedNativeChiralCauchyContinuousFeature j
        ⟨(x : ℝ)^(m+1), by
          exact ⟨pow_nonneg x.property.1 _,pow_le_one₀ x.property.1 x.property.2⟩⟩ := by
  have hx : 0 ≤ (x : ℝ) := x.property.1
  have hr : Real.sqrt ((m : ℝ)+1)*(Real.sqrt (x : ℝ)*(x : ℝ)^refinedAddress m j) =
      Real.sqrt (((m : ℝ)+1)*(x : ℝ)^m)*
        (Real.sqrt ((x : ℝ)^(m+1))*((x : ℝ)^(m+1))^j) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)]
    have he : (x : ℝ)^refinedAddress m j = (x : ℝ)^m*((x : ℝ)^(m+1))^j := by
      rw [← pow_mul,← pow_add]
      congr 1
      unfold refinedAddress
      omega
    rw [he,pow_succ (x : ℝ) m,Real.sqrt_mul (pow_nonneg hx m)]
    have hs := Real.sq_sqrt (pow_nonneg hx m)
    linear_combination -(Real.sqrt ((m : ℝ)+1)*Real.sqrt (x : ℝ)*
      (((x : ℝ)^m*(x : ℝ))^j))*hs
  simp only [completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk]
  exact_mod_cast hr

theorem power_column_inner (m i j : ℕ) :
    inner ℂ (powerColumn m i) (powerColumn m j) =
      inner ℂ (physicalCauchyFeature i) (physicalCauchyFeature j) := by
  unfold powerColumn
  rw [_root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),physical_column_inner,physical_column_inner]
  simp only [Complex.conj_ofReal]
  have hd : refinedAddress m i+refinedAddress m j+2 = (m+1)*(i+j+2) := by
    unfold refinedAddress
    ring
  rw [hd]
  have real_identity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Real.sqrt a*(Real.sqrt a*(a*b)⁻¹)=b⁻¹ := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt ha.le]
    field_simp
  have hr := real_identity ((m : ℝ)+1) ((i : ℝ)+j+2) (by positivity) (by positivity)
  convert congrArg Complex.ofReal hr using 1 <;> push_cast <;> ring

def powerSynthesis (m : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalCauchySpace :=
  Finsupp.linearCombination ℂ (powerColumn m)

theorem power_synthesis_inner (m : ℕ) (c d : ℕ →₀ ℂ) :
    inner ℂ (powerSynthesis m c) (powerSynthesis m d) =
      inner ℂ (physicalCauchyEmbedding c) (physicalCauchyEmbedding d) := by
  rw [embedding_sum,embedding_sum]
  simp only [powerSynthesis,Finsupp.linearCombination_apply,Finsupp.sum,
    sum_inner,inner_sum,_root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),power_column_inner]

theorem power_synthesis_norm (m : ℕ) (c : ℕ →₀ ℂ) :
    ‖powerSynthesis m c‖ = ‖physicalCauchyEmbedding c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),power_synthesis_inner]

def powerExtension (m : ℕ) : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  (powerSynthesis m).extendOfNorm physicalCauchyEmbedding

theorem power_extension_synthesis (m : ℕ) (c : ℕ →₀ ℂ) :
    powerExtension m (physicalCauchyEmbedding c) = powerSynthesis m c :=
  LinearMap.extendOfNorm_eq physicalCauchyEmbedding_dense
    ⟨1,fun c => by rw [one_mul,power_synthesis_norm]⟩ c

theorem power_extension_norm (m : ℕ) (x : PhysicalCauchySpace) :
    ‖powerExtension m x‖ = ‖x‖ := by
  refine physicalCauchyEmbedding_dense.induction_on x
    (isClosed_eq (powerExtension m).continuous.norm continuous_norm) ?_
  intro c
  rw [power_extension_synthesis,power_synthesis_norm]

def powerIsometry (m : ℕ) : PhysicalCauchySpace →ₗᵢ[ℂ] PhysicalCauchySpace :=
  { (powerExtension m).toLinearMap with norm_map' := power_extension_norm m }

theorem power_isometry_feature (m j : ℕ) :
    powerIsometry m (physicalCauchyFeature j) = powerColumn m j := by
  change powerExtension m (physicalCauchyEmbedding (Finsupp.single j 1)) = _
  rw [power_extension_synthesis]
  simp [powerSynthesis]

theorem power_isometry_inner (m : ℕ) (x y : PhysicalCauchySpace) :
    inner ℂ (powerIsometry m x) (powerIsometry m y) = inner ℂ x y :=
  (powerIsometry m).inner_map_map x y

end
end CarryRadialRefinement
