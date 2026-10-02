import GeometryOfNumbers.Analysis.RealCarryL2
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Real bracket, trace, return and exact Hilbert TFVD

Real rewrite of the historical vertical construction; no prime specialization.
The parameter eta is vertical and independent of center-leg deformation.
-/

open scoped BigOperators lp ENNReal NNReal

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

def carryVerticalL2EvalLinear (n : ℕ) : CarryVerticalL2 →ₗ[ℝ] ℝ where
  toFun x := x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def carryVerticalL2Eval (n : ℕ) : CarryVerticalL2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous (carryVerticalL2EvalLinear n) 1
    (fun x => by
      change ‖x n‖ ≤ 1 * ‖x‖
      simpa using lp.norm_apply_le_norm (p := (2 : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n)

@[simp] theorem carryVerticalL2Eval_apply
    (n : ℕ) (x : CarryVerticalL2) :
    carryVerticalL2Eval n x = x n := rfl

def carryVerticalL2ZeroHeadProjection :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  ContinuousLinearMap.id ℝ CarryVerticalL2 -
    (ContinuousLinearMap.toSpanSingleton ℝ
        (lp.single 2 0 (1 : ℝ)) ∘L carryVerticalL2Eval 0)

@[simp] theorem carryVerticalL2ZeroHeadProjection_apply
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2ZeroHeadProjection x n =
      if n = 0 then 0 else x n := by
  by_cases hn : n = 0
  · subst n
    simp [carryVerticalL2ZeroHeadProjection, lp.single_apply]
  · simp [carryVerticalL2ZeroHeadProjection, lp.single_apply, hn]

def carryWeightedVerticalCenteredBracketCore (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  ((eta : ℝ)⁻¹) • carryVerticalL2BackwardShift 1 -
    (2 : ℝ) • ContinuousLinearMap.id ℝ CarryVerticalL2 +
    (eta : ℝ) • carryVerticalL2UnilateralShift 1

@[simp] theorem carryWeightedVerticalCenteredBracketCore_apply
    (eta : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracketCore eta x n =
      (eta : ℝ)⁻¹ * x (n + 1) - 2 * x n +
        (eta : ℝ) * (if 1 ≤ n then x (n - 1) else 0) := by
  change
    (eta : ℝ)⁻¹ * x (n + 1) - 2 * x n +
        (eta : ℝ) * (carryVerticalL2UnilateralShift 1 x n) =
      (eta : ℝ)⁻¹ * x (n + 1) - 2 * x n +
        (eta : ℝ) * (if 1 ≤ n then x (n - 1) else 0)
  rw [carryVerticalL2UnilateralShift_apply]

def carryWeightedVerticalCenteredBracket (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  carryVerticalL2ZeroHeadProjection ∘L
    carryWeightedVerticalCenteredBracketCore eta

@[simp] theorem carryWeightedVerticalCenteredBracket_zero
    (eta : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalCenteredBracket eta x 0 = 0 := by
  simp [carryWeightedVerticalCenteredBracket]

@[simp] theorem carryWeightedVerticalCenteredBracket_succ
    (eta : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracket eta x (n + 1) =
      (eta : ℝ)⁻¹ * x (n + 2) - 2 * x (n + 1) +
        (eta : ℝ) * x n := by
  simp [carryWeightedVerticalCenteredBracket, Nat.add_assoc]

def carryWeightedVerticalTrace (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] (ℝ × ℝ) :=
  (carryVerticalL2Eval 0).prod
    (((eta : ℝ)⁻¹) • carryVerticalL2Eval 1 - carryVerticalL2Eval 0)

@[simp] theorem carryWeightedVerticalTrace_apply
    (eta : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalTrace eta x =
      (x 0, (eta : ℝ)⁻¹ * x 1 - x 0) := by
  simp [carryWeightedVerticalTrace]

end
end GeometryOfNumbers.Analysis.RealCarry

open scoped BigOperators lp ENNReal NNReal

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

def carryGeometricAmplitudeVector
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (eta : ℝ) ^ n, by
    have hsum : Summable (fun n : ℕ => ‖(eta : ℝ) ^ n‖) := by
      simpa [norm_pow, abs_of_nonneg heta0] using
        (summable_geometric_of_lt_one heta0 heta1)
    have hmem1 : Memℓp (fun n : ℕ => (eta : ℝ) ^ n) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsum
    exact hmem1.of_exponent_ge (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryGeometricAmplitudeVector_apply
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) (n : ℕ) :
    carryGeometricAmplitudeVector eta heta0 heta1 n = (eta : ℝ) ^ n := rfl

def carryAffineSlopeAmplitudeVector
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (carryWeightedVerticalGreenKernel eta n : ℝ), by
    have hsumReal : Summable (carryWeightedVerticalGreenKernel eta) :=
      carryWeightedVerticalGreenKernel_summable heta0 heta1
    have hsumNorm : Summable
        (fun n : ℕ => ‖(carryWeightedVerticalGreenKernel eta n : ℝ)‖) := by
      refine hsumReal.congr ?_
      intro n
      simp [abs_of_nonneg
        (carryWeightedVerticalGreenKernel_nonneg heta0 n)]
    have hmem1 : Memℓp
        (fun n : ℕ => (carryWeightedVerticalGreenKernel eta n : ℝ)) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsumNorm
    exact hmem1.of_exponent_ge (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryAffineSlopeAmplitudeVector_apply
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) (n : ℕ) :
    carryAffineSlopeAmplitudeVector eta heta0 heta1 n =
      (carryWeightedVerticalGreenKernel eta n : ℝ) := rfl

def carryWeightedVerticalReturn
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    (ℝ × ℝ) →L[ℝ] CarryVerticalL2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (carryGeometricAmplitudeVector eta heta0 heta1) ∘L
        ContinuousLinearMap.fst ℝ ℝ ℝ) +
  (ContinuousLinearMap.toSpanSingleton ℝ
      (carryAffineSlopeAmplitudeVector eta heta0 heta1) ∘L
        ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem carryWeightedVerticalReturn_apply
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (boundary : ℝ × ℝ) (n : ℕ) :
    carryWeightedVerticalReturn eta heta0 heta1 boundary n =
      (eta : ℝ) ^ n * (boundary.1 + (n : ℝ) * boundary.2) := by
  rcases boundary with ⟨a, b⟩
  simp [carryWeightedVerticalReturn,
    carryWeightedVerticalGreenKernel]
  ring

theorem carryWeightedVerticalTrace_comp_return
    (eta : ℝ) (hetapos : 0 < eta) (heta1 : eta < 1) :
    carryWeightedVerticalTrace eta ∘L
        carryWeightedVerticalReturn eta hetapos.le heta1 =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  apply ContinuousLinearMap.ext
  intro boundary
  rcases boundary with ⟨a, b⟩
  have hetaC : (eta : ℝ) ≠ 0 := hetapos.ne'
  apply Prod.ext
  · simp
  · simp [hetaC]

theorem carryWeightedVerticalCenteredBracket_comp_return
    (eta : ℝ) (hetapos : 0 < eta) (heta1 : eta < 1) :
    carryWeightedVerticalCenteredBracket eta ∘L
        carryWeightedVerticalReturn eta hetapos.le heta1 = 0 := by
  apply ContinuousLinearMap.ext
  intro boundary
  rcases boundary with ⟨a, b⟩
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have hetaC : (eta : ℝ) ≠ 0 := hetapos.ne'
      change
        carryWeightedVerticalCenteredBracket eta
            (carryWeightedVerticalReturn eta hetapos.le heta1 (a, b)) (n + 1) = 0
      rw [carryWeightedVerticalCenteredBracket_succ]
      simp only [carryWeightedVerticalReturn_apply]
      simp only [pow_succ]
      field_simp [hetaC]
      push_cast
      ring

end
end GeometryOfNumbers.Analysis.RealCarry

open scoped BigOperators lp ENNReal NNReal

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

def carryVerticalL2OperatorApply (x : CarryVerticalL2) :
    (CarryVerticalL2 →L[ℝ] CarryVerticalL2) →L[ℝ] CarryVerticalL2 :=
  LinearMap.mkContinuous
    { toFun := fun T => T x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖x‖
    (fun T => by
      simpa [mul_comm] using T.le_opNorm x)

@[simp] theorem carryVerticalL2OperatorApply_apply
    (x : CarryVerticalL2) (T : CarryVerticalL2 →L[ℝ] CarryVerticalL2) :
    carryVerticalL2OperatorApply x T = T x := rfl

def carryVerticalL2OperatorCoordinate
    (x : CarryVerticalL2) (n : ℕ) :
    (CarryVerticalL2 →L[ℝ] CarryVerticalL2) →L[ℝ] ℝ :=
  carryVerticalL2Eval n ∘L carryVerticalL2OperatorApply x

@[simp] theorem carryVerticalL2OperatorCoordinate_apply
    (x : CarryVerticalL2) (n : ℕ)
    (T : CarryVerticalL2 →L[ℝ] CarryVerticalL2) :
    carryVerticalL2OperatorCoordinate x n T = T x n := rfl

theorem carryVerticalL2WeightedGreen_apply
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen eta x n =
      ∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel eta r : ℝ) * x (n - r) := by
  have hsum : Summable (fun r : ℕ =>
      carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily eta r) :=
    carryWeightedVerticalGreenTerm_summable
      carryVerticalL2ShiftFamily heta0 heta1
  rw [carryVerticalL2WeightedGreen, carryWeightedVerticalGreen]
  change
    carryVerticalL2OperatorCoordinate x n
        (∑' r : ℕ,
          carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily eta r) = _
  rw [(carryVerticalL2OperatorCoordinate x n).map_tsum hsum]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun r hr => by
    have hrge : n + 1 ≤ r := by
      simpa only [Finset.mem_range, not_lt] using hr
    have hrnot : ¬r ≤ n := by omega
    simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
      carryVerticalL2UnilateralShift_apply, hrnot])]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < n + 1 := Finset.mem_range.mp hr
  have hrle : r ≤ n := by omega
  simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
    carryVerticalL2UnilateralShift_apply, hrle]

theorem carryVerticalL2WeightedGreen_apply_reindexed
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen eta x n =
      ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel eta (n - j) : ℝ) * x j := by
  rw [carryVerticalL2WeightedGreen_apply eta heta0 heta1]
  calc
    (∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel eta r : ℝ) * x (n - r)) =
      ∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel eta
            (n - (n + 1 - 1 - r)) : ℝ) *
          x (n + 1 - 1 - r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrlt : r < n + 1 := Finset.mem_range.mp hr
        have hrle : r ≤ n := by omega
        have hleft : n + 1 - 1 - r = n - r := by omega
        have hright : n - (n - r) = r := by omega
        rw [hleft, hright]
    _ = ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel eta (n - j) : ℝ) * x j :=
      Finset.sum_range_reflect
        (fun j =>
          (carryWeightedVerticalGreenKernel eta (n - j) : ℝ) * x j)
        (n + 1)

end

end GeometryOfNumbers.Analysis.RealCarry

open scoped BigOperators

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

def carryWeightedScalarFirstDifference
    (eta : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  eta⁻¹ * x (n + 1) - x n

def carryWeightedScalarSecondDifference
    (eta : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  carryWeightedScalarFirstDifference eta x (n + 1) -
    eta * carryWeightedScalarFirstDifference eta x n

theorem carryWeightedScalarSecondDifference_eq
    {eta : ℝ} (heta : eta ≠ 0) (x : ℕ → ℝ) (n : ℕ) :
    carryWeightedScalarSecondDifference eta x n =
      eta⁻¹ * x (n + 2) - 2 * x (n + 1) + eta * x n := by
  unfold carryWeightedScalarSecondDifference
    carryWeightedScalarFirstDifference
  simp only [Nat.add_assoc]
  field_simp [heta]
  ring

def carryWeightedScalarGreenSum
    (eta : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    ((n - 1 - j : ℕ) : ℝ) * eta ^ (n - 1 - j) *
      carryWeightedScalarSecondDifference eta x j

theorem carryWeightedScalarSecondDifference_telescope
    (eta : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      eta ^ (n - 1 - j) * carryWeightedScalarSecondDifference eta x j) =
        carryWeightedScalarFirstDifference eta x n -
          eta ^ n * carryWeightedScalarFirstDifference eta x 0 := by
  let d : ℕ → ℝ := fun k => carryWeightedScalarFirstDifference eta x k
  let F : ℕ → ℝ := fun k => eta ^ (n - k) * d k
  calc
    (∑ j ∈ Finset.range n,
      eta ^ (n - 1 - j) * carryWeightedScalarSecondDifference eta x j) =
        ∑ j ∈ Finset.range n, (F (j + 1) - F j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := Finset.mem_range.mp hj
          have hleft : n - (j + 1) = n - 1 - j := by omega
          have hright : n - j = (n - 1 - j) + 1 := by omega
          dsimp [F, d, carryWeightedScalarSecondDifference]
          rw [hleft, hright, pow_succ]
          ring
    _ = F (0 + n) - F 0 := by
      simpa using (Finset.sum_range_sub F n)
    _ = carryWeightedScalarFirstDifference eta x n -
          eta ^ n * carryWeightedScalarFirstDifference eta x 0 := by
      simp [F, d]

theorem carryWeightedScalarGreenSum_succ
    (eta : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    carryWeightedScalarGreenSum eta x (n + 1) =
      eta * carryWeightedScalarGreenSum eta x n +
        eta * (carryWeightedScalarFirstDifference eta x n -
          eta ^ n * carryWeightedScalarFirstDifference eta x 0) := by
  rw [← carryWeightedScalarSecondDifference_telescope eta x n]
  unfold carryWeightedScalarGreenSum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero,
    zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - j = (n - 1 - j) + 1 := by omega
  rw [hsub, pow_succ]
  push_cast
  ring

theorem carryWeightedScalarReconstruction
    {eta : ℝ} (heta : eta ≠ 0) (x : ℕ → ℝ) (n : ℕ) :
    x n =
      eta ^ n *
          (x 0 + (n : ℝ) * carryWeightedScalarFirstDifference eta x 0) +
        carryWeightedScalarGreenSum eta x n := by
  induction n with
  | zero =>
      simp [carryWeightedScalarGreenSum]
  | succ n ih =>
      calc
        x (n + 1) =
            eta * x n + eta * carryWeightedScalarFirstDifference eta x n := by
              unfold carryWeightedScalarFirstDifference
              field_simp [heta]
              ring
        _ = eta *
              (eta ^ n *
                  (x 0 + (n : ℝ) *
                    carryWeightedScalarFirstDifference eta x 0) +
                carryWeightedScalarGreenSum eta x n) +
              eta * carryWeightedScalarFirstDifference eta x n := by
                rw [ih]
        _ = eta ^ (n + 1) *
              (x 0 + ((n + 1 : ℕ) : ℝ) *
                carryWeightedScalarFirstDifference eta x 0) +
              carryWeightedScalarGreenSum eta x (n + 1) := by
                rw [carryWeightedScalarGreenSum_succ]
                rw [pow_succ]
                push_cast
                ring

end

end GeometryOfNumbers.Analysis.RealCarry

open scoped BigOperators lp ENNReal NNReal

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

theorem carryVerticalL2WeightedGreen_bracket_apply
    (eta : ℝ) (hetapos : 0 < eta) (heta1 : eta < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen eta
        (carryWeightedVerticalCenteredBracket eta x) n =
      carryWeightedScalarGreenSum (eta : ℝ) x n := by
  rw [carryVerticalL2WeightedGreen_apply_reindexed eta hetapos.le heta1]
  rw [Finset.sum_range_succ']
  simp only [carryWeightedVerticalCenteredBracket_zero, mul_zero, add_zero]
  unfold carryWeightedScalarGreenSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - (j + 1) = n - 1 - j := by omega
  have hetaC : (eta : ℝ) ≠ 0 := hetapos.ne'
  rw [hsub, carryWeightedVerticalCenteredBracket_succ,
    carryWeightedScalarSecondDifference_eq hetaC]
  simp [carryWeightedVerticalGreenKernel]

theorem carryWeightedVerticalTfvd_apply
    (eta : ℝ) (hetapos : 0 < eta) (heta1 : eta < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen eta
          (carryWeightedVerticalCenteredBracket eta x) n +
        carryWeightedVerticalReturn eta hetapos.le heta1
          (carryWeightedVerticalTrace eta x) n =
      x n := by
  rw [carryVerticalL2WeightedGreen_bracket_apply eta hetapos heta1]
  rw [carryWeightedVerticalReturn_apply,
    carryWeightedVerticalTrace_apply]
  have hetaC : (eta : ℝ) ≠ 0 := hetapos.ne'
  have hrec := carryWeightedScalarReconstruction
    (eta := (eta : ℝ)) hetaC (fun k => x k) n
  simpa [carryWeightedScalarFirstDifference, add_comm] using hrec.symm

theorem carryWeightedVerticalTfvd_identity
    (eta : ℝ) (hetapos : 0 < eta) (heta1 : eta < 1) :
    carryVerticalL2WeightedGreen eta ∘L
          carryWeightedVerticalCenteredBracket eta +
        carryWeightedVerticalReturn eta hetapos.le heta1 ∘L
          carryWeightedVerticalTrace eta =
      ContinuousLinearMap.id ℝ CarryVerticalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  simpa using carryWeightedVerticalTfvd_apply eta hetapos heta1 x n

end
end GeometryOfNumbers.Analysis.RealCarry
