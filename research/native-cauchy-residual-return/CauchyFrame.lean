import NativeDeflation

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

abbrev feature (k n : ℕ) : Physical := completedNativeRadialChiralCauchyState k n

/-- The original Cauchy kernel, without a change of scale or metric. -/
def cauchy (k i j : ℕ) : ℂ := ((k:ℂ)+1)/((i:ℂ)+(j:ℂ)+2)

theorem feature_inner (k i j : ℕ) : inner ℂ (feature k i) (feature k j) = cauchy k i j := by
  rw [inner_completedNativeRadialChiralCauchyState]
  simp [cauchy, div_eq_mul_inv]

theorem feature_projection (k n : ℕ) :
    nativeBoundaryProjection k (feature k n) = (2/((n:ℂ)+2)) • nativeAnchor k := by
  change (Submodule.span ℂ ({nativeAnchor k} : Set Physical)).starProjection _ = _
  rw [singleton_projection _ _ _ (ne_of_gt (anchorMass_pos k)) (nativeAnchor_inner k)]
  change ((anchorMass k:ℂ)⁻¹ * inner ℂ (feature k 0) (feature k n)) • _ = _
  rw [feature_inner]
  have hk : (k:ℂ)+1 ≠ 0 := by exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
  have hn : (n:ℂ)+2 ≠ 0 := by exact_mod_cast (show (n:ℝ)+2 ≠ 0 by positivity)
  congr 1
  simp only [anchorMass, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat, cauchy]
  norm_num only [Nat.cast_zero, zero_add]
  field_simp

def perpendicularFeature (k n : ℕ) : Physical :=
  feature k n - (2/((n:ℂ)+2)) • nativeAnchor k

theorem perpendicularFeature_eq_complement (k n : ℕ) :
    perpendicularFeature k n = feature k n-nativeBoundaryProjection k (feature k n) := by
  rw [feature_projection]; rfl

/-- Exact polarized Schur kernel of the ORIGINAL Cauchy family. -/
theorem perpendicularFeature_inner (k i j : ℕ) :
    inner ℂ (perpendicularFeature k i) (perpendicularFeature k j) =
      ((i:ℂ)/((i:ℂ)+2))*((j:ℂ)/((j:ℂ)+2))*cauchy k i j := by
  have hi : (i:ℂ)+2 ≠ 0 := by exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity)
  have hj : (j:ℂ)+2 ≠ 0 := by exact_mod_cast (show (j:ℝ)+2 ≠ 0 by positivity)
  have hij : (i:ℂ)+(j:ℂ)+2 ≠ 0 := by
    exact_mod_cast (show (i:ℝ)+(j:ℝ)+2 ≠ 0 by positivity)
  simp only [perpendicularFeature, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right]
  change inner ℂ (feature k i) (feature k j) -
    conj (2/((i:ℂ)+2)) * inner ℂ (feature k 0) (feature k j) -
    (2/((j:ℂ)+2)) * (inner ℂ (feature k i) (feature k 0) -
      conj (2/((i:ℂ)+2)) * inner ℂ (feature k 0) (feature k 0)) = _
  simp only [feature_inner, cauchy, map_div₀, map_add, map_natCast, map_ofNat,
    Nat.cast_zero, zero_add, add_zero]
  field_simp
  ring

/-- Forced by the previous Gram identity; not a fitted feature family. -/
def isometricFeature (k n : ℕ) : Physical :=
  (((n:ℂ)+2)/(n:ℂ)) • perpendicularFeature k n

theorem isometricFeature_inner (k i j : ℕ) (hi : i ≠ 0) (hj : j ≠ 0) :
    inner ℂ (isometricFeature k i) (isometricFeature k j) =
      inner ℂ (feature k i) (feature k j) := by
  have hi' : (i:ℂ) ≠ 0 := by exact_mod_cast hi
  have hj' : (j:ℂ) ≠ 0 := by exact_mod_cast hj
  have hip : (i:ℂ)+2 ≠ 0 := by exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity)
  have hjp : (j:ℂ)+2 ≠ 0 := by exact_mod_cast (show (j:ℝ)+2 ≠ 0 by positivity)
  simp only [isometricFeature, inner_smul_left, inner_smul_right,
    perpendicularFeature_inner, feature_inner, map_div₀, map_add, map_natCast, map_ofNat]
  field_simp

def tailSynthesis (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical where
  toFun c := ∑ i, c i • feature k (i.val+1)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

def isometricSynthesis (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical where
  toFun c := ∑ i, c i • isometricFeature k (i.val+1)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- All crosses, in two independently synthesized coefficient families. -/
theorem synthesis_isometry (k N : ℕ) (c d : Fin N → ℂ) :
    inner ℂ (isometricSynthesis k N c) (isometricSynthesis k N d) =
      inner ℂ (tailSynthesis k N c) (tailSynthesis k N d) := by
  simp only [isometricSynthesis, tailSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  have he (i j : Fin N) := isometricFeature_inner k (i.val+1) (j.val+1) (by omega) (by omega)
  simp_rw [he]

theorem synthesis_norm (k N : ℕ) (c : Fin N → ℂ) :
    ‖isometricSynthesis k N c‖ = ‖tailSynthesis k N c‖ := by
  have h := congrArg Complex.re (synthesis_isometry k N c c)
  rw [physical_inner_self_re, physical_inner_self_re] at h
  nlinarith [norm_nonneg (isometricSynthesis k N c), norm_nonneg (tailSynthesis k N c)]

theorem tailSynthesis_eq_original (k N : ℕ) (c : Fin N → ℂ) :
    tailSynthesis k N c = radialIncidentSynthesis k (N+1) (Fin.cons 0 c) := by
  simp [tailSynthesis, radialIncidentSynthesis, Fin.sum_univ_succ, feature]

theorem tailSynthesis_injective (k N : ℕ) : Function.Injective (tailSynthesis k N) := by
  intro c d h
  rw [tailSynthesis_eq_original, tailSynthesis_eq_original] at h
  have he := radialIncidentSynthesis_injective k (N+1) h
  funext i
  exact congrFun he i.succ

/-- A genuine isometry on the original finite source span. The domain norm
is inherited from the SAME physical carrier, not assigned by a target Gram. -/
def finitePhysicalIsometry (k N : ℕ) : (tailSynthesis k N).range →ₗᵢ[ℂ] Physical where
  toLinearMap := (isometricSynthesis k N).comp
    (LinearEquiv.ofInjective (tailSynthesis k N) (tailSynthesis_injective k N)).symm.toLinearMap
  norm_map' x := by
    obtain ⟨c,rfl⟩ := (LinearEquiv.ofInjective (tailSynthesis k N)
      (tailSynthesis_injective k N)).surjective x
    change ‖isometricSynthesis k N
      ((LinearEquiv.ofInjective (tailSynthesis k N) (tailSynthesis_injective k N)).symm
        ((LinearEquiv.ofInjective (tailSynthesis k N) (tailSynthesis_injective k N)) c))‖ =
      ‖tailSynthesis k N c‖
    rw [LinearEquiv.symm_apply_apply]
    exact synthesis_norm k N c

theorem finitePhysicalIsometry_exact (k N : ℕ) (c : Fin N → ℂ) :
    finitePhysicalIsometry k N ⟨tailSynthesis k N c, ⟨c,rfl⟩⟩ = isometricSynthesis k N c := by
  change isometricSynthesis k N
    ((LinearEquiv.ofInjective (tailSynthesis k N) (tailSynthesis_injective k N)).symm
      ((LinearEquiv.ofInjective (tailSynthesis k N) (tailSynthesis_injective k N)) c)) = _
  rw [LinearEquiv.symm_apply_apply]

end
end CarryCauchyResidual
