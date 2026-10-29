import AddressPort
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdFinite

/-! The existing finite scalar TFVD, lifted coordinatewise to the three
retained channels. There is no replacement Hilbert norm or missing boundary
datum. All Green pairings use the pre-existing greenForm. -/
namespace CarryMaterialTheta
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def resolvedThetaLift (N : ℕ) (f : Fin N → ℂ) (u : ℝ) : Fin N → MaterialThetaPort :=
  fun i => materialThetaMode (i.val+1) (f i) u

def thetaLift (N : ℕ) (f : Fin N → ℂ) (u : ℝ) : MaterialThetaPort :=
  ∑ i : Fin N, resolvedThetaLift N f u i

theorem resolvedThetaLift_injective (N : ℕ) (u : ℝ) :
    Function.Injective (fun f : Fin N → ℂ => resolvedThetaLift N f u) := by
  intro f g h
  funext i
  exact materialThetaMode_injective (i.val+1) u (congrFun h i)

/-- Independent physical leg/camera labels are retained separately from the
arithmetic address. Encoding a leg as a different integer address is avoided. -/
def resolvedLabeledThetaLift {ι : Type*} (N : ℕ)
    (f : ι → Fin N → ℂ) (u : ℝ) : ι → Fin N → MaterialThetaPort :=
  fun leg => resolvedThetaLift N (f leg) u

theorem resolvedLabeledThetaLift_injective {ι : Type*} (N : ℕ) (u : ℝ) :
    Function.Injective (fun f : ι → Fin N → ℂ => resolvedLabeledThetaLift N f u) := by
  intro f g h
  funext leg
  exact resolvedThetaLift_injective N u (congrFun h leg)

def thetaLiftLinear (N : ℕ) (u : ℝ) : (Fin N → ℂ) →ₗ[ℂ] MaterialThetaPort where
  toFun f := thetaLift N f u
  map_add' f g := by
    simp only [thetaLift, resolvedThetaLift, materialThetaMode, Pi.add_apply,
      add_mul, ← Prod.mk_add_mk, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [thetaLift, resolvedThetaLift, materialThetaMode, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_assoc, Prod.smul_mk,
      Finset.smul_sum]

/-- Return and Green are literal coordinatewise lifts of the existing finite
TFVD expressions. Both initial data are retained in `portReturn`. -/
def portFirstDifference (q : ℂ) (X : ℕ → MaterialThetaPort) (k : ℕ) : MaterialThetaPort :=
  q⁻¹ • X (k+1) - X k

def portSecondDifference (q : ℂ) (X : ℕ → MaterialThetaPort) (k : ℕ) : MaterialThetaPort :=
  portFirstDifference q X (k+1) - q • portFirstDifference q X k

def portReturn (q : ℂ) (X : ℕ → MaterialThetaPort) (k : ℕ) : MaterialThetaPort :=
  q^k • (X 0 + (k : ℂ) • portFirstDifference q X 0)

def portGreen (q : ℂ) (X : ℕ → MaterialThetaPort) (k : ℕ) : MaterialThetaPort :=
  ∑ j ∈ Finset.range k,
    (((k-1-j : ℕ) : ℂ)*q^(k-1-j)) • portSecondDifference q X j

theorem port_tfvd {q : ℂ} (hq : q ≠ 0) (X : ℕ → MaterialThetaPort) (k : ℕ) :
    X k = portReturn q X k + portGreen q X k := by
  ext
  · simpa only [portReturn, portGreen, portFirstDifference, portSecondDifference,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sum, Prod.snd_sum, smul_eq_mul,
      carryWeightedScalarFirstDifference, carryWeightedScalarSecondDifference,
      carryWeightedScalarGreenSum, mul_assoc] using
      (carryWeightedScalarReconstruction hq (fun j => (X j).1) k)
  · simpa only [portReturn, portGreen, portFirstDifference, portSecondDifference,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sum, Prod.snd_sum, smul_eq_mul,
      carryWeightedScalarFirstDifference, carryWeightedScalarSecondDifference,
      carryWeightedScalarGreenSum, mul_assoc] using
      (carryWeightedScalarReconstruction hq (fun j => (X j).2.1) k)
  · simpa only [portReturn, portGreen, portFirstDifference, portSecondDifference,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sum, Prod.snd_sum, smul_eq_mul,
      carryWeightedScalarFirstDifference, carryWeightedScalarSecondDifference,
      carryWeightedScalarGreenSum, mul_assoc] using
      (carryWeightedScalarReconstruction hq (fun j => (X j).2.2) k)

/-- Naturality under the ACTUAL finite theta lift, not a requested identity
inserted as a field. In particular both trace coordinates commute with it. -/
theorem thetaLift_firstDifference (N : ℕ) (q : ℂ)
    (X : ℕ → Fin N → ℂ) (u : ℝ) (k : ℕ) :
    thetaLift N (fun i => carryWeightedScalarFirstDifference q (fun j => X j i) k) u =
      portFirstDifference q (fun j => thetaLift N (X j) u) k := by
  change thetaLiftLinear N u (q⁻¹ • X (k+1) - X k) = _
  rw [map_sub, map_smul]
  rfl

theorem thetaLift_secondDifference (N : ℕ) (q : ℂ)
    (X : ℕ → Fin N → ℂ) (u : ℝ) (k : ℕ) :
    thetaLift N (fun i => carryWeightedScalarSecondDifference q (fun j => X j i) k) u =
      portSecondDifference q (fun j => thetaLift N (X j) u) k := by
  change thetaLiftLinear N u
    ((fun i => carryWeightedScalarFirstDifference q (fun j => X j i) (k+1)) -
      q • (fun i => carryWeightedScalarFirstDifference q (fun j => X j i) k)) = _
  rw [map_sub, map_smul]
  change thetaLift N _ u - q • thetaLift N _ u = _
  rw [thetaLift_firstDifference, thetaLift_firstDifference]
  rfl

theorem thetaLift_return (N : ℕ) (q : ℂ) (X : ℕ → Fin N → ℂ) (u : ℝ) (k : ℕ) :
    thetaLift N (fun i => q^k *
      (X 0 i + (k : ℂ)*carryWeightedScalarFirstDifference q (fun j => X j i) 0)) u =
      portReturn q (fun j => thetaLift N (X j) u) k := by
  change thetaLiftLinear N u (q^k •
    (X 0 + (k : ℂ) • (fun i => carryWeightedScalarFirstDifference q (fun j => X j i) 0))) = _
  rw [map_smul, map_add, map_smul]
  change q^k • (thetaLift N (X 0) u + (k : ℂ) • thetaLift N _ u) = _
  rw [thetaLift_firstDifference]
  rfl

theorem thetaLift_green (N : ℕ) (q : ℂ) (X : ℕ → Fin N → ℂ) (u : ℝ) (k : ℕ) :
    thetaLift N (fun i => carryWeightedScalarGreenSum q (fun j => X j i) k) u =
      portGreen q (fun j => thetaLift N (X j) u) k := by
  have he : (fun i => carryWeightedScalarGreenSum q (fun j => X j i) k) =
      ∑ j ∈ Finset.range k, (((k-1-j : ℕ) : ℂ)*q^(k-1-j)) •
        (fun i => carryWeightedScalarSecondDifference q (fun t => X t i) j) := by
    funext i
    simp only [carryWeightedScalarGreenSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change thetaLiftLinear N u _ = _
  rw [map_sum]
  unfold portGreen
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change _ • thetaLift N _ u = _
  rw [thetaLift_secondDifference]

def logPort (p : MaterialThetaPort) : ℂ × ℂ := (p.1,p.2.1)
def derivativePort (p : MaterialThetaPort) : ℂ × ℂ := (p.1,p.2.2)

/-- Reconstructed before pairing. All four ordered crossings survive for
independent inputs and independent finite TFVD depths. -/
theorem tfvd_log_green_four_crosses {q r : ℂ} (hq : q ≠ 0) (hr : r ≠ 0)
    (X Y : ℕ → MaterialThetaPort) (k l : ℕ) :
    greenForm (𝕜 := ℂ) (logPort (X k)) (logPort (Y l)) =
      greenForm (𝕜 := ℂ) (logPort (portGreen q X k)) (logPort (portGreen r Y l)) +
      greenForm (𝕜 := ℂ) (logPort (portGreen q X k)) (logPort (portReturn r Y l)) +
      greenForm (𝕜 := ℂ) (logPort (portReturn q X k)) (logPort (portGreen r Y l)) +
      greenForm (𝕜 := ℂ) (logPort (portReturn q X k)) (logPort (portReturn r Y l)) := by
  rw [port_tfvd hq X k, port_tfvd hr Y l]
  change greenForm (𝕜 := ℂ)
    (logPort (portReturn q X k) + logPort (portGreen q X k))
    (logPort (portReturn r Y l) + logPort (portGreen r Y l)) = _
  rw [greenForm_add_left, greenForm_add_right, greenForm_add_right]
  ring

theorem real_shear_preserves_green (c : ℝ) (x y : ℂ × ℂ) :
    greenForm (𝕜 := ℂ) (x.1,x.2+(c : ℂ)*x.1) (y.1,y.2+(c : ℂ)*y.1) =
      greenForm (𝕜 := ℂ) x y := by
  simp only [greenForm, RCLike.inner_apply', map_add, map_mul, Complex.conj_ofReal]
  ring

theorem theta_mode_log_green_dilation {b n m : ℕ} (hb : 0 < b)
    (hn : 0 < n) (hm : 0 < m) (a d : ℂ) (u : ℝ) :
    greenForm (𝕜 := ℂ)
      (logPort (materialThetaMode (b*n) a u))
      (logPort (materialThetaMode (b*m) d u)) =
      (primeCarryAmplitudeRatio b : ℂ)^2 *
        greenForm (𝕜 := ℂ)
          (logPort (materialThetaMode n a (u+Real.log (b : ℝ))))
          (logPort (materialThetaMode m d (u+Real.log (b : ℝ)))) := by
  rw [materialThetaMode_dilation hb hn, materialThetaMode_dilation hb hm]
  change greenForm (𝕜 := ℂ)
    ((primeCarryAmplitudeRatio b : ℂ) •
      ((logPort (materialThetaMode n a (u+Real.log (b : ℝ)))).1,
       (logPort (materialThetaMode n a (u+Real.log (b : ℝ)))).2 +
       (Real.log (b : ℝ) : ℂ)*(logPort (materialThetaMode n a (u+Real.log (b : ℝ)))).1))
    ((primeCarryAmplitudeRatio b : ℂ) •
      ((logPort (materialThetaMode m d (u+Real.log (b : ℝ)))).1,
       (logPort (materialThetaMode m d (u+Real.log (b : ℝ)))).2 +
       (Real.log (b : ℝ) : ℂ)*(logPort (materialThetaMode m d (u+Real.log (b : ℝ)))).1)) = _
  simp only [greenForm, RCLike.inner_apply', Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, map_add, map_mul, Complex.conj_ofReal]
  ring

end
end CarryMaterialTheta
