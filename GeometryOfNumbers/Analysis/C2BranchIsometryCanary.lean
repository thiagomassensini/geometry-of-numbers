import GeometryOfNumbers.Analysis.C2BranchOrbitCanary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Real Hilbert realization of the pure C2 branch operator

Historical specification: formalizacao_C2, dc35555879e3c0f188508c729c4a0ea31be246fb,
operadores/cp_branch_operator.py. Python is not a proof dependency.
The branch labels record the two signed directions, and j explicitly denotes
depth j+2. Both labels receive the same pure radial-angular orbit. This does
not identify the distinct physical leg phases with their logarithmic defects.
The sigma family remains a downstream comparison family.

RealPlaneState keeps its original coordinate energy and instances. The new
Euclidean Hilbert carrier is related to it by an algebraic linear equivalence;
its squared norm is proved equal to the existing energy. No TFVD, Green or
whitening identity is used to prove the branch norm formula.
-/

open scoped BigOperators lp ENNReal

namespace GeometryOfNumbers.Analysis
noncomputable section

abbrev RealPlaneHilbert := EuclideanSpace ℝ (Fin 2)

/-- 0 labels the negative branch and 1 the positive branch. -/
abbrev C2BranchDirection := Fin 2

def c2BranchDirectionSign (a : C2BranchDirection) : ℤ :=
  if a = 0 then -1 else 1

theorem c2BranchDirectionSign_values :
    c2BranchDirectionSign 0 = -1 ∧ c2BranchDirectionSign 1 = 1 := by
  norm_num [c2BranchDirectionSign]

abbrev C2BranchCarrier := ℓ²(C2BranchDirection × ℕ, RealPlaneHilbert)

/-- Algebraic equivalence only: the original product norm is not Euclidean. -/
def realPlaneHilbertEquiv : RealPlaneState ≃ₗ[ℝ] RealPlaneHilbert where
  toFun v := WithLp.toLp 2 ![v.1, v.2]
  invFun v := (v 0, v 1)
  left_inv v := rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

theorem realPlaneHilbert_energy_eq_norm_sq (v : RealPlaneHilbert) :
    realPlaneEnergy (realPlaneHilbertEquiv.symm v) = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [realPlaneEnergy, realPlaneHilbertEquiv, Fin.sum_univ_two]

def c2DeformedFiberStepLinear (sigma t : ℝ) : RealPlaneState →ₗ[ℝ] RealPlaneState where
  toFun := c2DeformedFiberStep sigma t
  map_add' v w := by
    apply Prod.ext <;> simp [c2DeformedFiberStep, scaleRealPlane, rotateRealPlane] <;> ring
  map_smul' c v := by
    apply Prod.ext <;> simp [c2DeformedFiberStep, scaleRealPlane, rotateRealPlane] <;> ring

private theorem iterate_add (sigma t : ℝ) (k : ℕ) (v w : RealPlaneState) :
    (c2DeformedFiberStep sigma t)^[k] (v + w) =
      (c2DeformedFiberStep sigma t)^[k] v + (c2DeformedFiberStep sigma t)^[k] w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact (c2DeformedFiberStepLinear sigma t).map_add _ _

private theorem iterate_smul (sigma t : ℝ) (k : ℕ) (c : ℝ) (v : RealPlaneState) :
    (c2DeformedFiberStep sigma t)^[k] (c • v) =
      c • (c2DeformedFiberStep sigma t)^[k] v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact (c2DeformedFiberStepLinear sigma t).map_smul c _

theorem c2DeformedFiberStep_iterate_eq_radial_rotation
    (sigma t : ℝ) (k : ℕ) (v : RealPlaneState) :
    (c2DeformedFiberStep sigma t)^[k] v =
      scaleRealPlane ((2 : ℝ) ^ (-(k : ℝ) * sigma))
        (rotateRealPlane (-(k : ℝ) * t * Real.log 2) v) := by
  have h : (c2DeformedFiberStep sigma t)^[k] v =
      scaleRealPlane (c2RadialAmplitudeRatio sigma ^ k)
        (rotateRealPlane ((k : ℝ) * (-t * Real.log 2)) v) := by
    induction k with
    | zero => simp [scaleRealPlane, rotateRealPlane_zero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have hang : ((k + 1 : ℕ) : ℝ) * (-t * Real.log 2) =
          -t * Real.log 2 + (k : ℝ) * (-t * Real.log 2) := by push_cast; ring
      rw [hang, rotateRealPlane_add, pow_succ]
      apply Prod.ext <;> simp [c2DeformedFiberStep, scaleRealPlane, rotateRealPlane] <;> ring
  rw [h]
  have hamp : c2RadialAmplitudeRatio sigma ^ k = (2 : ℝ) ^ (-(k : ℝ) * sigma) := by
    unfold c2RadialAmplitudeRatio
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hamp]
  congr 2
  ring

/-- The literal branch coordinates before the Hilbert membership proof. -/
def realBranchCoordinates (sigma t : ℝ) (v : RealPlaneHilbert)
    (i : C2BranchDirection × ℕ) : RealPlaneHilbert :=
  realPlaneHilbertEquiv
    ((c2DeformedFiberStep sigma t)^[i.2 + 2] (realPlaneHilbertEquiv.symm v))

theorem realBranchCoordinates_norm_sq (sigma t : ℝ) (v : RealPlaneHilbert)
    (i : C2BranchDirection × ℕ) :
    ‖realBranchCoordinates sigma t v i‖ ^ 2 =
      c2RadialEnergyRatio sigma ^ (i.2 + 2) * ‖v‖ ^ 2 := by
  rw [← realPlaneHilbert_energy_eq_norm_sq]
  simp only [realBranchCoordinates, LinearEquiv.symm_apply_apply]
  rw [c2DeformedFiberStep_iterate_energy, realPlaneHilbert_energy_eq_norm_sq]

theorem realBranchCoordinates_square_summable (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) :
    Summable (fun i : C2BranchDirection × ℕ => ‖realBranchCoordinates sigma t v i‖ ^ 2) := by
  have hj : Summable (fun j : ℕ => c2RadialEnergyRatio sigma ^ (j + 2)) := by
    simpa only [c2DeformedUnitOrbit_energy] using c2BranchUnitOrbitEnergy_summable sigma t hsigma
  simp only [realBranchCoordinates_norm_sq]
  exact (summable_prod_of_nonneg (fun i =>
    mul_nonneg (pow_nonneg (c2RadialEnergyRatio_pos sigma).le _) (sq_nonneg _))).mpr
    ⟨fun _ => hj.mul_right _, (hasSum_fintype _).summable⟩

theorem realBranchCoordinates_mem_l2 (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) : Memℓp (realBranchCoordinates sigma t v) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simpa [Real.rpow_two] using realBranchCoordinates_square_summable sigma t hsigma v

def realBranchOperator (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) : C2BranchCarrier :=
  ⟨realBranchCoordinates sigma t v, realBranchCoordinates_mem_l2 sigma t hsigma v⟩

theorem realBranchOperator_apply (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) (a : C2BranchDirection) (j : ℕ) :
    realPlaneHilbertEquiv.symm (realBranchOperator sigma t hsigma v (a, j)) =
      (c2DeformedFiberStep sigma t)^[j + 2] (realPlaneHilbertEquiv.symm v) := by
  exact realPlaneHilbertEquiv.symm_apply_apply _

theorem realBranchOperator_apply_closed_form (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) (a : C2BranchDirection) (j : ℕ) :
    realPlaneHilbertEquiv.symm (realBranchOperator sigma t hsigma v (a, j)) =
      scaleRealPlane ((2 : ℝ) ^ (-((j + 2 : ℕ) : ℝ) * sigma))
        (rotateRealPlane (-((j + 2 : ℕ) : ℝ) * t * Real.log 2)
          (realPlaneHilbertEquiv.symm v)) := by
  rw [realBranchOperator_apply, c2DeformedFiberStep_iterate_eq_radial_rotation]

def realBranchOperatorLinear (sigma t : ℝ) (hsigma : 0 < sigma) :
    RealPlaneHilbert →ₗ[ℝ] C2BranchCarrier where
  toFun := realBranchOperator sigma t hsigma
  map_add' v w := by
    ext i r
    simp [realBranchOperator, realBranchCoordinates, map_add, iterate_add]
  map_smul' c v := by
    ext i r
    simp [realBranchOperator, realBranchCoordinates, map_smul, iterate_smul]

theorem realBranchOperator_norm_sq (sigma t : ℝ) (hsigma : 0 < sigma)
    (v : RealPlaneHilbert) :
    ‖realBranchOperator sigma t hsigma v‖ ^ 2 =
      c2BranchOrbitMass sigma t * realPlaneEnergy (realPlaneHilbertEquiv.symm v) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hn := lp.norm_rpow_eq_tsum hp (realBranchOperator sigma t hsigma v)
  have hs := realBranchCoordinates_square_summable sigma t hsigma v
  have hts := hs.tsum_prod
  simp only [realBranchCoordinates_norm_sq] at hts
  have hnorm : ‖realBranchOperator sigma t hsigma v‖ ^ 2 =
      ∑' i : C2BranchDirection × ℕ, c2RadialEnergyRatio sigma ^ (i.2 + 2) * ‖v‖ ^ 2 := by
    simpa [Real.rpow_two, realBranchOperator, realBranchCoordinates_norm_sq] using hn
  rw [hnorm, hts, tsum_fintype]
  simp only [Fin.sum_univ_two, tsum_mul_right]
  rw [c2BranchOrbitMass_eq_geometric_series, realPlaneHilbert_energy_eq_norm_sq]
  ring

theorem realBranchOperator_norm_sq_eq_legacyBranchNormSq (sigma t : ℝ)
    (hsigma : 0 < sigma) (v : RealPlaneHilbert) :
    ‖realBranchOperator sigma t hsigma v‖ ^ 2 =
      legacyC2BranchNormSq sigma * realPlaneEnergy (realPlaneHilbertEquiv.symm v) := by
  rw [realBranchOperator_norm_sq, c2BranchOrbitMass_eq_legacyBranchNormSq]

theorem realBranchOperator_norm_sq_of_realPlaneState (sigma t : ℝ)
    (hsigma : 0 < sigma) (v : RealPlaneState) :
    ‖realBranchOperator sigma t hsigma (realPlaneHilbertEquiv v)‖ ^ 2 =
      c2BranchOrbitMass sigma t * realPlaneEnergy v := by
  rw [realBranchOperator_norm_sq, LinearEquiv.symm_apply_apply]

theorem realBranchOperator_norm_independent_time (sigma t₁ t₂ : ℝ)
    (hsigma : 0 < sigma) (v : RealPlaneHilbert) :
    ‖realBranchOperator sigma t₁ hsigma v‖ = ‖realBranchOperator sigma t₂ hsigma v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [realBranchOperator_norm_sq, realBranchOperator_norm_sq,
    c2BranchOrbitMass_independent_time sigma t₁ t₂]

theorem realCriticalBranchOperator_norm (t : ℝ) (v : RealPlaneHilbert) :
    ‖realBranchOperator ((1 : ℝ) / 2) t (by norm_num) v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [realBranchOperator_norm_sq, c2BranchOrbitMass_half, one_mul,
    realPlaneHilbert_energy_eq_norm_sq]

def realCriticalBranchIsometry (t : ℝ) : RealPlaneHilbert →ₗᵢ[ℝ] C2BranchCarrier :=
  { realBranchOperatorLinear ((1 : ℝ) / 2) t (by norm_num) with
    norm_map' := realCriticalBranchOperator_norm t }

theorem realCriticalBranchIsometry_apply_centerStep (t : ℝ) (v : RealPlaneHilbert)
    (a : C2BranchDirection) (j : ℕ) :
    realPlaneHilbertEquiv.symm (realCriticalBranchIsometry t v (a, j)) =
      (c2CenterFiberStep t)^[j + 2] (realPlaneHilbertEquiv.symm v) := by
  change realPlaneHilbertEquiv.symm
    (realBranchOperator ((1 : ℝ) / 2) t (by norm_num) v (a, j)) = _
  rw [realBranchOperator_apply, c2DeformedFiberStep_half_eq_c2CenterFiberStep]

theorem realCriticalBranch_adjoint_comp_self (t : ℝ) :
    (realCriticalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      (realCriticalBranchIsometry t).toContinuousLinearMap = 1 :=
  (realCriticalBranchIsometry t).adjoint_comp_self

end
end GeometryOfNumbers.Analysis
