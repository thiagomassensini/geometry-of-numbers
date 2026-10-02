import GeometryOfNumbers.Analysis.RealProjectiveGreenValve

/-! # Normalized projective mass and curvature equivalence

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.ProjectiveValve

open PowerSeries
open GeometryOfNumbers.Analysis.ProjectiveDepth
open GeometryOfNumbers.Analysis.TowerValve
open GeometryOfNumbers.Analysis.GreenValve

variable {K : Type*} [Field K] [CharZero K]

noncomputable def projectiveValveMass (D : PowerSeries K) : PowerSeries K :=
  projectiveGreenMass (fromProjective D)

@[simp] theorem projectiveValveMass_constantCoeff (D : PowerSeries K) :
    constantCoeff (projectiveValveMass D) = 1 := by
  unfold projectiveValveMass
  exact projectiveGreenMass_constantCoeff (fromProjective D)

theorem derivative_projectiveValveMass (D : PowerSeries K) :
    d⁄dX K (projectiveValveMass D) = D * projectiveValveMass D := by
  unfold projectiveValveMass
  rw [derivative_projectiveGreenMass]
  rw [toProjective_fromProjective]

theorem normalized_projective_ode_unique
    (D A B : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hB0 : constantCoeff B = 1)
    (hA : d⁄dX K A = D * A)
    (hB : d⁄dX K B = D * B) :
    A = B := by
  let a : ℕ → K := fun n => coeff n A
  let b : ℕ → K := fun n => coeff n B
  let channel : ℕ → K := fun n => coeff n (X * D)

  have hmkA : mk a = A := by
    ext n
    simp [a]
  have hmkB : mk b = B := by
    ext n
    simp [b]
  have hmkChannel : mk channel = X * D := by
    ext n
    simp [channel]

  have hlogA : IsLogDerivChannel A (X * D) := by
    unfold IsLogDerivChannel
    change (X * D) * A = X * (d⁄dX K A)
    rw [hA]
    ac_rfl
  have hlogB : IsLogDerivChannel B (X * D) := by
    unfold IsLogDerivChannel
    change (X * D) * B = X * (d⁄dX K B)
    rw [hB]
    ac_rfl

  have hTowerA : IsTowerChannel a channel := by
    apply (isTowerChannel_iff_isLogDerivChannel a channel).mpr
    rw [hmkA, hmkChannel]
    exact hlogA
  have hTowerB : IsTowerChannel b channel := by
    apply (isTowerChannel_iff_isLogDerivChannel b channel).mpr
    rw [hmkB, hmkChannel]
    exact hlogB

  have ha0 : a 0 = 1 := by
    dsimp [a]
    rw [coeff_zero_eq_constantCoeff_apply, hA0]
  have hb0 : b 0 = 1 := by
    dsimp [b]
    rw [coeff_zero_eq_constantCoeff_apply, hB0]

  have hab : a = b :=
    towerMass_unique a b channel ha0 hb0 hTowerA hTowerB

  calc
    A = mk a := hmkA.symm
    _ = mk b := congrArg (fun s : ℕ → K => mk s) hab
    _ = B := hmkB

theorem projectiveValveMass_unique
    (D A : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hA : d⁄dX K A = D * A) :
    A = projectiveValveMass D := by
  exact normalized_projective_ode_unique D A (projectiveValveMass D)
    hA0 (projectiveValveMass_constantCoeff D)
    hA (derivative_projectiveValveMass D)

theorem existsUnique_projectiveValveMass (D : PowerSeries K) :
    ∃! A : PowerSeries K,
      constantCoeff A = 1 ∧ d⁄dX K A = D * A := by
  refine ⟨projectiveValveMass D, ?_, ?_⟩
  · exact ⟨projectiveValveMass_constantCoeff D,
      derivative_projectiveValveMass D⟩
  · intro A hA
    exact projectiveValveMass_unique D A hA.1 hA.2

@[simp] theorem projectiveValveMass_toProjective (C : PowerSeries K) :
    projectiveValveMass (toProjective C) = projectiveGreenMass C := by
  unfold projectiveValveMass
  rw [fromProjective_toProjective]

end GeometryOfNumbers.Analysis.ProjectiveValve

namespace GeometryOfNumbers.Analysis.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K]

noncomputable def projectiveValveCurvature
    (A : PowerSeries K) : PowerSeries K :=
  (d⁄dX K A) * A⁻¹

theorem projectiveValveCurvature_mul_self
    (A : PowerSeries K)
    (hA0 : constantCoeff A = 1) :
    projectiveValveCurvature A * A = d⁄dX K A := by
  have hA0ne : constantCoeff A ≠ 0 := by
    rw [hA0]
    exact one_ne_zero
  unfold projectiveValveCurvature
  rw [mul_assoc, PowerSeries.inv_mul_cancel A hA0ne, mul_one]

theorem projectiveValveCurvature_eq_of_ode
    (D A : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hA : d⁄dX K A = D * A) :
    projectiveValveCurvature A = D := by
  have hA0ne : constantCoeff A ≠ 0 := by
    rw [hA0]
    exact one_ne_zero
  unfold projectiveValveCurvature
  rw [hA, mul_assoc, PowerSeries.mul_inv_cancel A hA0ne, mul_one]

variable [CharZero K]

@[simp] theorem projectiveValveCurvature_projectiveValveMass
    (D : PowerSeries K) :
    projectiveValveCurvature (projectiveValveMass D) = D := by
  exact projectiveValveCurvature_eq_of_ode D (projectiveValveMass D)
    (projectiveValveMass_constantCoeff D)
    (derivative_projectiveValveMass D)

@[simp] theorem projectiveValveMass_projectiveValveCurvature
    (A : PowerSeries K)
    (hA0 : constantCoeff A = 1) :
    projectiveValveMass (projectiveValveCurvature A) = A := by
  exact (projectiveValveMass_unique
    (projectiveValveCurvature A) A hA0
    (projectiveValveCurvature_mul_self A hA0).symm).symm

def NormalizedProjectiveMass (K : Type*) [Field K] :=
  {A : PowerSeries K // constantCoeff A = 1}

noncomputable def projectiveValveEquiv :
    PowerSeries K ≃ NormalizedProjectiveMass K where
  toFun D := ⟨projectiveValveMass D, projectiveValveMass_constantCoeff D⟩
  invFun A := projectiveValveCurvature A.1
  left_inv := by
    intro D
    exact projectiveValveCurvature_projectiveValveMass D
  right_inv := by
    intro A
    apply Subtype.ext
    exact projectiveValveMass_projectiveValveCurvature A.1 A.2

theorem projectiveValveMass_injective :
    Function.Injective (projectiveValveMass : PowerSeries K → PowerSeries K) := by
  intro D E hDE
  have h := congrArg projectiveValveCurvature hDE
  simpa using h

theorem projectiveValveCurvature_surjective :
    Function.Surjective
      (fun A : NormalizedProjectiveMass K => projectiveValveCurvature A.1) := by
  intro D
  refine ⟨⟨projectiveValveMass D, projectiveValveMass_constantCoeff D⟩, ?_⟩
  exact projectiveValveCurvature_projectiveValveMass D

end GeometryOfNumbers.Analysis.ProjectiveValve

namespace GeometryOfNumbers.Analysis.ProjectiveValve

open PowerSeries
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

@[simp] theorem projectiveValveMass_zero :
    projectiveValveMass (0 : PowerSeries K) = 1 := by
  symm
  exact projectiveValveMass_unique (0 : PowerSeries K) 1
    (by simp) (by simp)

theorem projectiveValveMass_add (D E : PowerSeries K) :
    projectiveValveMass (D + E) =
      projectiveValveMass D * projectiveValveMass E := by
  symm
  apply projectiveValveMass_unique (D + E)
    (projectiveValveMass D * projectiveValveMass E)
  · simp
  · have hD := derivative_projectiveValveMass D
    have hE := derivative_projectiveValveMass E
    change (projectiveValveMass D).derivativeFun =
      D * projectiveValveMass D at hD
    change (projectiveValveMass E).derivativeFun =
      E * projectiveValveMass E at hE
    change (projectiveValveMass D * projectiveValveMass E).derivativeFun =
      (D + E) * (projectiveValveMass D * projectiveValveMass E)
    rw [PowerSeries.derivativeFun_mul, hD, hE]
    simp only [smul_eq_mul]
    ring

end GeometryOfNumbers.Analysis.ProjectiveValve
