import GeometryOfNumbers.Analysis.RealTowerValve

/-! # Projective coordinate, Green Jacobian cancellation, and potential

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.ProjectiveDepth

open PowerSeries
open GeometryOfNumbers.Analysis.DiscreteValve

variable {R : Type*} [CommRing R]

noncomputable def coordinate : PowerSeries R :=
  X * geometricSeries

@[simp] theorem coordinate_constantCoeff :
    constantCoeff (coordinate (R := R)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coordinate]
  simp

theorem one_sub_X_mul_coordinate :
    (1 - X) * coordinate (R := R) = X := by
  rw [coordinate]
  calc
    ((1 : PowerSeries R) - X) * (X * geometricSeries) =
        X * (((1 : PowerSeries R) - X) * geometricSeries) := by
      ac_rfl
    _ = X := by
      rw [one_sub_X_mul_geometricSeries, mul_one]

theorem one_add_coordinate_eq_geometricSeries :
    1 + coordinate (R := R) = geometricSeries := by
  rw [coordinate]
  calc
    (1 : PowerSeries R) + X * geometricSeries =
        ((1 : PowerSeries R) - X) * geometricSeries + X * geometricSeries := by
      rw [one_sub_X_mul_geometricSeries]
    _ = geometricSeries := by
      rw [sub_mul, one_mul, sub_add_cancel]

theorem geometricSeries_mul_self_eq_greenKernelSeries :
    (geometricSeries : PowerSeries R) * geometricSeries = greenKernelSeries := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [geometricSeries, greenKernelSeries]

theorem coordinate_derivativeFun :
    (coordinate (R := R)).derivativeFun = greenKernelSeries := by
  ext n
  rw [coeff_derivativeFun, coordinate, coeff_succ_X_mul,
    geometricSeries, coeff_mk, greenKernelSeries, coeff_mk]
  ring

noncomputable def greenVelocity : PowerSeries R :=
  X * greenKernelSeries

theorem euler_coordinate :
    X * (coordinate (R := R)).derivativeFun = greenVelocity := by
  rw [coordinate_derivativeFun]
  rfl

theorem greenVelocity_eq_coordinate_mul_one_add :
    greenVelocity (R := R) =
      coordinate * (1 + coordinate) := by
  calc
    greenVelocity (R := R) = X * greenKernelSeries := rfl
    _ = X * (geometricSeries * geometricSeries) := by
      rw [geometricSeries_mul_self_eq_greenKernelSeries]
    _ = coordinate * geometricSeries := by
      simp [coordinate, mul_assoc]
    _ = coordinate * (1 + coordinate) := by
      rw [one_add_coordinate_eq_geometricSeries]

theorem coordinate_sq_eq_X_sq_mul_greenKernelSeries :
    coordinate (R := R) ^ 2 = X ^ 2 * greenKernelSeries := by
  rw [coordinate, ← geometricSeries_mul_self_eq_greenKernelSeries]
  ring

theorem euler_subst_coordinate (F : PowerSeries R) :
    X * d⁄dX R (F.subst (coordinate (R := R))) =
      greenVelocity *
        ((d⁄dX R F).subst (coordinate (R := R))) := by
  have hcoordinate : HasSubst (coordinate (R := R)) :=
    HasSubst.of_constantCoeff_zero' coordinate_constantCoeff
  rw [derivative_subst R hcoordinate]
  change
      X * ((d⁄dX R F).subst (coordinate (R := R)) *
          (coordinate (R := R)).derivativeFun) =
        greenVelocity * ((d⁄dX R F).subst (coordinate (R := R)))
  rw [coordinate_derivativeFun]
  unfold greenVelocity
  ac_rfl

end GeometryOfNumbers.Analysis.ProjectiveDepth

namespace GeometryOfNumbers.Analysis.ProjectiveDepth

open PowerSeries
open GeometryOfNumbers.Analysis.DiscreteValve

variable {R : Type*} [CommRing R]

noncomputable def inverseGeometricSeries : PowerSeries R :=
  mk fun n => (-1 : R) ^ n

theorem one_add_X_mul_inverseGeometricSeries :
    (1 + X) * inverseGeometricSeries = (1 : R⟦X⟧) := by
  ext n
  cases n with
  | zero =>
      simp [inverseGeometricSeries]
  | succ n =>
      simp only [add_mul, one_mul, map_add, coeff_succ_X_mul,
        inverseGeometricSeries, coeff_mk, coeff_one, Nat.succ_ne_zero,
        ↓reduceIte]
      rw [pow_succ]
      ring

noncomputable def inverseCoordinate : PowerSeries R :=
  X * inverseGeometricSeries

@[simp] theorem inverseCoordinate_constantCoeff :
    constantCoeff (inverseCoordinate (R := R)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, inverseCoordinate]
  simp

theorem one_add_X_mul_inverseCoordinate :
    (1 + X) * inverseCoordinate (R := R) = X := by
  rw [inverseCoordinate]
  calc
    ((1 : PowerSeries R) + X) * (X * inverseGeometricSeries) =
        X * (((1 : PowerSeries R) + X) * inverseGeometricSeries) := by
      ac_rfl
    _ = X := by
      rw [one_add_X_mul_inverseGeometricSeries, mul_one]

theorem one_sub_inverseCoordinate_eq_inverseGeometricSeries :
    1 - inverseCoordinate (R := R) = inverseGeometricSeries := by
  rw [inverseCoordinate]
  rw [← one_add_X_mul_inverseGeometricSeries (R := R)]
  ring

theorem coordinate_hasSubst :
    HasSubst (coordinate (R := R)) :=
  HasSubst.of_constantCoeff_zero' coordinate_constantCoeff

theorem inverseCoordinate_hasSubst :
    HasSubst (inverseCoordinate (R := R)) :=
  HasSubst.of_constantCoeff_zero' inverseCoordinate_constantCoeff

theorem coordinate_subst_inverseCoordinate :
    (coordinate (R := R)).subst (inverseCoordinate (R := R)) = X := by
  have hinverse : HasSubst (inverseCoordinate (R := R)) :=
    inverseCoordinate_hasSubst
  have htransportRaw := congrArg
    (fun F : PowerSeries R => F.subst (inverseCoordinate (R := R)))
    (one_sub_X_mul_coordinate (R := R))
  have hsubOne : PowerSeries.subst (a := inverseCoordinate (R := R)) (1 : PowerSeries R) =
      C (1 : R) := by
    change PowerSeries.subst (a := inverseCoordinate (R := R)) (C (1 : R)) = C (1 : R)
    simpa using
      (PowerSeries.subst_C (S := R) (a := inverseCoordinate (R := R)) (r := (1 : R)))
  have htransport :
      (C (1 : R) - inverseCoordinate (R := R)) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R))) =
        inverseCoordinate (R := R) := by
    simpa [subst_mul hinverse, subst_sub hinverse, subst_X hinverse, hsubOne] using
      htransportRaw
  have htransport' : (1 - inverseCoordinate (R := R)) *
      ((coordinate (R := R)).subst (inverseCoordinate (R := R))) =
    inverseCoordinate (R := R) := by
    simpa using htransport
  calc
    (coordinate (R := R)).subst (inverseCoordinate (R := R)) =
        ((1 + X) * (1 - inverseCoordinate (R := R))) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R))) := by
      rw [one_sub_inverseCoordinate_eq_inverseGeometricSeries,
        one_add_X_mul_inverseGeometricSeries, one_mul]
    _ = (1 + X) *
        ((1 - inverseCoordinate (R := R)) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R)))) := by
      ring
    _ = (1 + X) * inverseCoordinate (R := R) := by
      rw [htransport']
    _ = X := one_add_X_mul_inverseCoordinate

theorem inverseCoordinate_subst_coordinate :
    (inverseCoordinate (R := R)).subst (coordinate (R := R)) = X := by
  have hcoordinate : HasSubst (coordinate (R := R)) :=
    coordinate_hasSubst
  have htransportRaw := congrArg
    (fun F : PowerSeries R => F.subst (coordinate (R := R)))
    (one_add_X_mul_inverseCoordinate (R := R))
  have hsubOne : PowerSeries.subst (a := coordinate (R := R)) (1 : PowerSeries R) =
      C (1 : R) := by
    change PowerSeries.subst (a := coordinate (R := R)) (C (1 : R)) = C (1 : R)
    simpa using
      (PowerSeries.subst_C (S := R) (a := coordinate (R := R)) (r := (1 : R)))
  have htransport :
      (C (1 : R) + coordinate (R := R)) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R))) =
        coordinate (R := R) := by
    simpa [subst_mul hcoordinate, subst_add hcoordinate, subst_X hcoordinate, hsubOne] using
      htransportRaw
  have htransport' : (1 + coordinate (R := R)) *
      ((inverseCoordinate (R := R)).subst (coordinate (R := R))) =
    coordinate (R := R) := by
    simpa using htransport
  calc
    (inverseCoordinate (R := R)).subst (coordinate (R := R)) =
        ((1 - X) * (1 + coordinate (R := R))) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R))) := by
      rw [one_add_coordinate_eq_geometricSeries,
        one_sub_X_mul_geometricSeries, one_mul]
    _ = (1 - X) *
        ((1 + coordinate (R := R)) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R)))) := by
      ring
    _ = (1 - X) * coordinate (R := R) := by
      rw [htransport']
    _ = X := one_sub_X_mul_coordinate

end GeometryOfNumbers.Analysis.ProjectiveDepth

namespace GeometryOfNumbers.Analysis.ProjectiveDepth

open PowerSeries

variable {R : Type*} [CommRing R]

theorem subst_X_eq_self (F : PowerSeries R) :
    F.subst (X : PowerSeries R) = F := by
  have h := PowerSeries.map_algebraMap_eq_subst_X (R := R) (S := R) F
  simp [h.symm]

noncomputable def toProjective (F : PowerSeries R) : PowerSeries R :=
  F.subst (inverseCoordinate (R := R))

noncomputable def fromProjective (F : PowerSeries R) : PowerSeries R :=
  F.subst (coordinate (R := R))

@[simp] theorem fromProjective_toProjective (F : PowerSeries R) :
    fromProjective (toProjective F) = F := by
  unfold fromProjective toProjective
  rw [PowerSeries.subst_comp_subst_apply
    (inverseCoordinate_hasSubst (R := R))
    (coordinate_hasSubst (R := R))]
  rw [inverseCoordinate_subst_coordinate (R := R)]
  exact subst_X_eq_self F

@[simp] theorem toProjective_fromProjective (F : PowerSeries R) :
    toProjective (fromProjective F) = F := by
  unfold fromProjective toProjective
  rw [PowerSeries.subst_comp_subst_apply
    (coordinate_hasSubst (R := R))
    (inverseCoordinate_hasSubst (R := R))]
  rw [coordinate_subst_inverseCoordinate (R := R)]
  exact subst_X_eq_self F

noncomputable def coordinateChangeEquiv :
    PowerSeries R ≃ PowerSeries R where
  toFun := toProjective
  invFun := fromProjective
  left_inv := fromProjective_toProjective
  right_inv := toProjective_fromProjective

theorem toProjective_add (F G : PowerSeries R) :
    toProjective (F + G) = toProjective F + toProjective G := by
  unfold toProjective
  exact PowerSeries.subst_add (inverseCoordinate_hasSubst (R := R)) F G

theorem toProjective_mul (F G : PowerSeries R) :
    toProjective (F * G) = toProjective F * toProjective G := by
  unfold toProjective
  exact PowerSeries.subst_mul (inverseCoordinate_hasSubst (R := R)) F G

theorem fromProjective_add (F G : PowerSeries R) :
    fromProjective (F + G) = fromProjective F + fromProjective G := by
  unfold fromProjective
  exact PowerSeries.subst_add (coordinate_hasSubst (R := R)) F G

theorem fromProjective_mul (F G : PowerSeries R) :
    fromProjective (F * G) = fromProjective F * fromProjective G := by
  unfold fromProjective
  exact PowerSeries.subst_mul (coordinate_hasSubst (R := R)) F G

theorem coordinate_inverse_jacobian :
    ((d⁄dX R (coordinate (R := R))).subst
        (inverseCoordinate (R := R))) *
      d⁄dX R (inverseCoordinate (R := R)) = 1 := by
  have h := congrArg (fun F : PowerSeries R => d⁄dX R F)
    (coordinate_subst_inverseCoordinate (R := R))
  rw [PowerSeries.derivative_subst R
      (inverseCoordinate_hasSubst (R := R)),
    PowerSeries.derivative_X] at h
  exact h

theorem inverse_coordinate_jacobian :
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      d⁄dX R (coordinate (R := R)) = 1 := by
  have h := congrArg (fun F : PowerSeries R => d⁄dX R F)
    (inverseCoordinate_subst_coordinate (R := R))
  rw [PowerSeries.derivative_subst R
      (coordinate_hasSubst (R := R)),
    PowerSeries.derivative_X] at h
  exact h

theorem greenKernel_subst_inverse_mul_inverseDerivative :
    (PowerSeries.subst (a := inverseCoordinate (R := R))
        (f := (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R))) ) *
      d⁄dX R (inverseCoordinate (R := R)) = 1 := by
  have hcoordDeriv :
      d⁄dX R (coordinate (R := R)) =
        (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R)) := by
    calc
      d⁄dX R (coordinate (R := R)) = (coordinate (R := R)).derivativeFun := rfl
      _ = (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R)) := coordinate_derivativeFun (R := R)
  have hsub : (PowerSeries.subst (a := inverseCoordinate (R := R))
      (f := d⁄dX R (coordinate (R := R))) *
        d⁄dX R (inverseCoordinate (R := R)) = 1) := by
    simpa using (coordinate_inverse_jacobian (R := R))
  calc
    (PowerSeries.subst (a := inverseCoordinate (R := R))
        (f := (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R))) ) *
        d⁄dX R (inverseCoordinate (R := R))
        = (PowerSeries.subst (a := inverseCoordinate (R := R))
            (f := d⁄dX R (coordinate (R := R))) *
              d⁄dX R (inverseCoordinate (R := R))) := by
      apply congrArg (fun F => F * d⁄dX R (inverseCoordinate (R := R)))
      exact congrArg (PowerSeries.subst (a := inverseCoordinate (R := R))) hcoordDeriv.symm
    _ = 1 := hsub

theorem inverseDerivative_subst_coordinate_mul_greenKernel :
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R)) = 1 := by
  have hcoordDeriv :
      d⁄dX R (coordinate (R := R)) =
        (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R)) := by
    calc
      d⁄dX R (coordinate (R := R)) = (coordinate (R := R)).derivativeFun := rfl
      _ = (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R)) := coordinate_derivativeFun (R := R)
  have hsub : (d⁄dX R (inverseCoordinate (R := R))).subst
      (coordinate (R := R)) * (d⁄dX R (coordinate (R := R))) = 1 := by
    simpa using (inverse_coordinate_jacobian (R := R))
  calc
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      (GeometryOfNumbers.Analysis.DiscreteValve.greenKernelSeries (R := R))
      = (d⁄dX R (inverseCoordinate (R := R))).subst
          (coordinate (R := R)) * (d⁄dX R (coordinate (R := R))) := by
        exact congrArg (fun F =>
          (d⁄dX R (inverseCoordinate (R := R))).subst (coordinate (R := R)) * F) hcoordDeriv.symm
    _ = 1 := hsub

end GeometryOfNumbers.Analysis.ProjectiveDepth

namespace GeometryOfNumbers.Analysis.GreenValve

open PowerSeries
open GeometryOfNumbers.Analysis.ProjectiveDepth
open GeometryOfNumbers.Analysis.DiscreteValve
open GeometryOfNumbers.Analysis.TowerValve

variable {K : Type*} [Field K]

noncomputable def greenChannelSeries (C : PowerSeries K) : PowerSeries K :=
  greenVelocity (R := K) * C

noncomputable def greenChannel (C : PowerSeries K) : ℕ → K :=
  fun n => coeff n (greenChannelSeries C)

@[simp] theorem greenChannel_zero (C : PowerSeries K) :
    greenChannel C 0 = 0 := by
  simp [greenChannel, greenChannelSeries,
    GeometryOfNumbers.Analysis.ProjectiveDepth.greenVelocity,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem mk_greenChannel (C : PowerSeries K) :
    mk (greenChannel C) = greenChannelSeries C := by
  ext n
  simp [greenChannel]

noncomputable def greenLogPotential (C : PowerSeries K) : PowerSeries K :=
  logIntegral (greenChannel C)

@[simp] theorem greenLogPotential_constantCoeff (C : PowerSeries K) :
    constantCoeff (greenLogPotential C) = 0 := by
  unfold greenLogPotential
  exact constantCoeff_logIntegral (greenChannel C)

variable [CharZero K]

theorem X_mul_derivative_greenLogPotential (C : PowerSeries K) :
    X * (d⁄dX K (greenLogPotential C)) = greenChannelSeries C := by
  unfold greenLogPotential
  change X * (logIntegral (greenChannel C)).derivativeFun = greenChannelSeries C
  rw [X_mul_derivativeFun_logIntegral (greenChannel C) (greenChannel_zero C)]
  exact mk_greenChannel C

theorem derivative_greenLogPotential (C : PowerSeries K) :
    d⁄dX K (greenLogPotential C) =
      greenKernelSeries (R := K) * C := by
  apply PowerSeries.X_mul_cancel
  calc
    X * (d⁄dX K (greenLogPotential C)) =
        greenChannelSeries C :=
      X_mul_derivative_greenLogPotential C
    _ = X * (greenKernelSeries (R := K) * C) := by
      unfold greenChannelSeries
      unfold GeometryOfNumbers.Analysis.ProjectiveDepth.greenVelocity
      ac_rfl

theorem derivative_toProjective_greenLogPotential (C : PowerSeries K) :
    d⁄dX K (toProjective (greenLogPotential C)) = toProjective C := by
  have hinverse : HasSubst (inverseCoordinate (R := K)) :=
    inverseCoordinate_hasSubst
  unfold toProjective
  rw [PowerSeries.derivative_subst K hinverse]
  rw [derivative_greenLogPotential C]
  rw [PowerSeries.subst_mul hinverse]
  calc
    (((greenKernelSeries (R := K)).subst (inverseCoordinate (R := K))) *
          (C.subst (inverseCoordinate (R := K)))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      (((greenKernelSeries (R := K)).subst (inverseCoordinate (R := K))) *
          d⁄dX K (inverseCoordinate (R := K))) *
        (C.subst (inverseCoordinate (R := K))) := by
      ac_rfl
    _ = 1 * (C.subst (inverseCoordinate (R := K))) := by
      rw [greenKernel_subst_inverse_mul_inverseDerivative (R := K)]
    _ = C.subst (inverseCoordinate (R := K)) := by
      rw [one_mul]

end GeometryOfNumbers.Analysis.GreenValve

namespace GeometryOfNumbers.Analysis.ProjectiveDepth

open PowerSeries

variable {R : Type*} [CommRing R]

theorem constantCoeff_toProjective (F : PowerSeries R) :
    constantCoeff (toProjective F) = constantCoeff F := by
  have hinverse : HasSubst (inverseCoordinate (R := R)) :=
    inverseCoordinate_hasSubst
  unfold toProjective
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hinverse,
    finsum_eq_single _ 0 fun d hd => by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow,
        inverseCoordinate_constantCoeff, zero_pow hd, smul_zero]]
  simp [coeff_zero_eq_constantCoeff_apply]

end GeometryOfNumbers.Analysis.ProjectiveDepth

namespace GeometryOfNumbers.Analysis.GreenValve

open PowerSeries
open GeometryOfNumbers.Analysis.ProjectiveDepth
open GeometryOfNumbers.Analysis.TowerValve

variable {K : Type*} [Field K] [CharZero K]

noncomputable def greenMassSeries (C : PowerSeries K) : PowerSeries K :=
  expSeries (greenLogPotential C)

@[simp] theorem greenMassSeries_constantCoeff (C : PowerSeries K) :
    constantCoeff (greenMassSeries C) = 1 := by
  unfold greenMassSeries
  exact constantCoeff_expSeries (greenLogPotential C)
    (greenLogPotential_constantCoeff C)

theorem isLogDerivChannel_greenMassSeries (C : PowerSeries K) :
    IsLogDerivChannel (greenMassSeries C) (greenChannelSeries C) := by
  unfold greenMassSeries
  have h := isLogDerivChannel_expSeries (greenLogPotential C)
    (greenLogPotential_constantCoeff C)
  have hgrad := X_mul_derivative_greenLogPotential C
  change X * (greenLogPotential C).derivativeFun = greenChannelSeries C at hgrad
  rwa [hgrad] at h

theorem mk_towerMass_greenChannel (C : PowerSeries K) :
    mk (towerMass (greenChannel C)) = greenMassSeries C := by
  rw [mk_towerMass_eq_expSeries (greenChannel C) (greenChannel_zero C)]
  rfl

theorem derivative_greenMassSeries (C : PowerSeries K) :
    d⁄dX K (greenMassSeries C) =
      greenMassSeries C * d⁄dX K (greenLogPotential C) := by
  apply PowerSeries.X_mul_cancel
  have hchannel := isLogDerivChannel_greenMassSeries C
  unfold IsLogDerivChannel at hchannel
  calc
    X * (d⁄dX K (greenMassSeries C)) =
        greenChannelSeries C * greenMassSeries C := hchannel.symm
    _ = (X * (d⁄dX K (greenLogPotential C))) * greenMassSeries C := by
      rw [X_mul_derivative_greenLogPotential C]
    _ = X * (greenMassSeries C * d⁄dX K (greenLogPotential C)) := by
      ac_rfl

noncomputable def projectiveGreenMass (C : PowerSeries K) : PowerSeries K :=
  toProjective (greenMassSeries C)

@[simp] theorem projectiveGreenMass_constantCoeff (C : PowerSeries K) :
    constantCoeff (projectiveGreenMass C) = 1 := by
  unfold projectiveGreenMass
  rw [constantCoeff_toProjective, greenMassSeries_constantCoeff]

theorem derivative_projectiveGreenMass (C : PowerSeries K) :
    d⁄dX K (projectiveGreenMass C) =
      toProjective C * projectiveGreenMass C := by
  have hinverse : HasSubst (inverseCoordinate (R := K)) :=
    inverseCoordinate_hasSubst
  have hpotential :
      ((d⁄dX K (greenLogPotential C)).subst
          (inverseCoordinate (R := K))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      C.subst (inverseCoordinate (R := K)) := by
    have h := derivative_toProjective_greenLogPotential C
    unfold toProjective at h
    rw [PowerSeries.derivative_subst K hinverse] at h
    exact h
  unfold projectiveGreenMass toProjective
  rw [PowerSeries.derivative_subst K hinverse]
  rw [derivative_greenMassSeries C]
  rw [PowerSeries.subst_mul hinverse]
  calc
    (((greenMassSeries C).subst (inverseCoordinate (R := K))) *
          ((d⁄dX K (greenLogPotential C)).subst
            (inverseCoordinate (R := K)))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      ((greenMassSeries C).subst (inverseCoordinate (R := K))) *
        (((d⁄dX K (greenLogPotential C)).subst
            (inverseCoordinate (R := K))) *
          d⁄dX K (inverseCoordinate (R := K))) := by
      ac_rfl
    _ = ((greenMassSeries C).subst (inverseCoordinate (R := K))) *
        (C.subst (inverseCoordinate (R := K))) := by
      rw [hpotential]
    _ = (C.subst (inverseCoordinate (R := K))) *
        ((greenMassSeries C).subst (inverseCoordinate (R := K))) := by
      ac_rfl

end GeometryOfNumbers.Analysis.GreenValve
