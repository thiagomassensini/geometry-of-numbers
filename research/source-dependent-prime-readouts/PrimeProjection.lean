import CPFormal.Analytic.CpPrimeCarryDefectReadoutCrosswalk
import Mathlib.Tactic

/-! Finite orthogonal extraction using the ORIGINAL prime-carry axes and
canonical dual axes. Readouts depend linearly on the input state. This is
not a replacement metric or an identification with the completed Green form. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Original centered-carry observation, now explicitly input-dependent. -/
def primeReadout (p : Nat.Primes) (X : PrimeCarryDefectGlobalHilbert) : ℝ :=
  inner ℝ (primeCriticalCenteredCarryGlobalAxis p) X

/-- Finite projection in the original direct sum of prime residue fibers. -/
def primeProjection (S : Finset Nat.Primes) :
    PrimeCarryDefectGlobalHilbert →ₗ[ℝ] PrimeCarryDefectGlobalHilbert := by
  classical
  exact {
    toFun := fun X => ∑ p ∈ S, lp.single 2 p
      (primeReadout p X • primeCriticalCenteredCarryDualAxis p)
    map_add' := by
      intro X Y
      simp only [primeReadout,inner_add_right,add_smul,lp.single_add,Finset.sum_add_distrib]
    map_smul' := by
      intro a X
      simp only [primeReadout,real_inner_smul_right,mul_smul,lp.single_smul,Finset.smul_sum,RingHom.id_apply]
  }

theorem prime_projection_apply (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) (p : Nat.Primes) :
    primeProjection S X p=if p∈S then
      primeReadout p X • primeCriticalCenteredCarryDualAxis p else 0 := by
  classical
  change (∑ q ∈ S, lp.single 2 q
    (primeReadout q X • primeCriticalCenteredCarryDualAxis q)) p=_
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem prime_projection_zero (S : Finset Nat.Primes) : primeProjection S 0=0 :=
  (primeProjection S).map_zero

theorem prime_projection_add (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    primeProjection S (X+Y)=primeProjection S X+primeProjection S Y :=
  (primeProjection S).map_add X Y

theorem prime_projection_smul (S : Finset Nat.Primes)
    (a : ℝ) (X : PrimeCarryDefectGlobalHilbert) :
    primeProjection S (a • X)=a • primeProjection S X :=
  (primeProjection S).map_smul a X

/-- The active readouts are preserved, with no fixed affine realization premise. -/
theorem prime_readout_projection (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) (p : Nat.Primes) :
    primeReadout p (primeProjection S X)=if p∈S then primeReadout p X else 0 := by
  classical
  unfold primeReadout
  rw [inner_primeCriticalCenteredCarryGlobalAxis,prime_projection_apply]
  split_ifs with hp
  · rw [inner_smul_right,inner_primeCriticalCenteredCarryAxis_dualAxis,mul_one]
    rfl
  · exact inner_zero_right _

theorem prime_projection_idempotent (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) :
    primeProjection S (primeProjection S X)=primeProjection S X := by
  classical
  apply lp.ext
  funext p
  rw [prime_projection_apply,prime_projection_apply,prime_readout_projection]
  by_cases hp : p∈S <;> simp [hp]

/-- Canonical dual pairing with an arbitrary state, in the original fiber. -/
theorem prime_dual_pairing (p : Nat.Primes) (Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeCriticalCenteredCarryDualAxis p) (Y p)=
      ((p:ℝ)/((p:ℝ)-1))*primeReadout p Y := by
  unfold primeCriticalCenteredCarryDualAxis primeReadout
  rw [real_inner_smul_left,inner_primeCriticalCenteredCarryGlobalAxis]

/-- Exact polarization of the finite readout ledger. -/
theorem prime_projection_pairing (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeProjection S X) Y=
      ∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*primeReadout p X*primeReadout p Y := by
  classical
  change inner ℝ (∑ p∈S, lp.single 2 p
    (primeReadout p X • primeCriticalCenteredCarryDualAxis p)) Y=_
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro p _
  rw [lp.inner_single_left,real_inner_smul_left,prime_dual_pairing]
  ring

theorem prime_projection_self_adjoint (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeProjection S X) Y=inner ℝ X (primeProjection S Y) := by
  calc
    _ = ∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*primeReadout p X*primeReadout p Y :=
      prime_projection_pairing S X Y
    _ = ∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*primeReadout p Y*primeReadout p X := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = inner ℝ (primeProjection S Y) X := (prime_projection_pairing S Y X).symm
    _ = _ := real_inner_comm _ _

theorem prime_projection_projected_pairing (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeProjection S X) (primeProjection S Y)=
      ∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*primeReadout p X*primeReadout p Y := by
  classical
  rw [prime_projection_pairing]
  apply Finset.sum_congr rfl
  intro p hp
  rw [prime_readout_projection,if_pos hp]

/-- Both cross terms vanish separately, before diagonal or scalar norm readout. -/
theorem prime_projection_residual_pairing (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeProjection S X) (Y-primeProjection S Y)=0 := by
  rw [inner_sub_right,prime_projection_pairing,prime_projection_projected_pairing,sub_self]

theorem prime_residual_projection_pairing (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (X-primeProjection S X) (primeProjection S Y)=0 := by
  rw [real_inner_comm,prime_projection_residual_pairing]

/-- Lossless bilinear identity in this carrier; no claim of native Green sign. -/
theorem prime_projection_polarized_pythagoras (S : Finset Nat.Primes)
    (X Y : PrimeCarryDefectGlobalHilbert) :
    inner ℝ X Y=inner ℝ (primeProjection S X) (primeProjection S Y)+
      inner ℝ (X-primeProjection S X) (Y-primeProjection S Y) := by
  have hxy := prime_projection_residual_pairing S X Y
  have hyx := prime_residual_projection_pairing S X Y
  rw [inner_sub_right] at hxy
  rw [inner_sub_left] at hyx
  rw [inner_sub_left,inner_sub_right,inner_sub_right]
  linarith

theorem prime_projection_norm_sq (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) :
    ‖X‖^2=‖primeProjection S X‖^2+‖X-primeProjection S X‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using prime_projection_polarized_pythagoras S X X

/-- Extraction never increases the ORIGINAL norm. -/
theorem prime_projection_norm_sq_le (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) : ‖primeProjection S X‖^2≤‖X‖^2 := by
  have h := prime_projection_norm_sq S X
  nlinarith [sq_nonneg ‖X-primeProjection S X‖]

theorem prime_projection_norm_le (S : Finset Nat.Primes)
    (X : PrimeCarryDefectGlobalHilbert) : ‖primeProjection S X‖≤‖X‖ := by
  have h := prime_projection_norm_sq_le S X
  nlinarith [norm_nonneg X,norm_nonneg (primeProjection S X)]

/-- Growing an atlas does not change any previously extracted coordinate. -/
theorem prime_projection_nested (S T : Finset Nat.Primes) (hST : S⊆T)
    (X : PrimeCarryDefectGlobalHilbert) :
    primeProjection S (primeProjection T X)=primeProjection S X := by
  classical
  apply lp.ext
  funext p
  rw [prime_projection_apply,prime_projection_apply,prime_readout_projection]
  by_cases hp : p∈S
  · rw [if_pos hp,if_pos hp,if_pos (hST hp)]
  · rw [if_neg hp,if_neg hp]

theorem prime_projection_nested_reverse (S T : Finset Nat.Primes) (hST : S⊆T)
    (X : PrimeCarryDefectGlobalHilbert) :
    primeProjection T (primeProjection S X)=primeProjection S X := by
  classical
  apply lp.ext
  funext p
  rw [prime_projection_apply,prime_projection_apply,prime_readout_projection]
  by_cases hp : p∈S
  · rw [if_pos hp,if_pos hp,if_pos (hST hp)]
  · by_cases hpT : p∈T <;> simp [hp,hpT]

end
end CarrySourcePrime
