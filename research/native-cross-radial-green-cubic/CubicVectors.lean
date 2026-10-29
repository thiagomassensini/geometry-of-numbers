import PartTaylor
import GreenRegression

namespace CarryGreenCubic
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl
open CarrySpatialCorrection CarryEnergyCorrection CarryCrossRadial CarryGreenLeading NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Specialization of the source-derived law at cubic ADDRESS degree. -/
theorem seed_cubic_compensation (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    cubicProfile eta h0 h1 (nativeEvenProfile 0) 0=
      (8:ℂ) • constantPart eta h0 h1 (nativeEvenProfile 0) 0 ∧
    cubicProfile eta h0 h1 (nativeEvenProfile 0) 1=
      constantPart eta h0 h1 (nativeEvenProfile 0) 1 ∧
    cubicProfile eta h0 h1 (nativeEvenProfile 0) 2=
      (-7:ℂ) • constantPart eta h0 h1 (nativeEvenProfile 0) 0 := by
  simpa only [cubicProfile,show (2:ℂ)^3=8 by norm_num,
    show (1:ℂ)-8= -7 by norm_num] using seed_address_compensation 3 eta h0 h1

/-- A cubic physical profile is nonzero without assuming h1 or Hankel signs. -/
theorem seed_cubic_residual_ne_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    cubicProfile eta h0 h1 (nativeEvenProfile 0) 2≠0 := by
  have hc : constantPart eta h0 h1 (nativeEvenProfile 0) 0≠0 := by
    intro hz
    have he := (even_vector_compensation eta h0 h1).2.2
    rw [hz,neg_zero] at he
    exact linear_even_residual_ne_zero eta h0 h1 he
  rw [(seed_cubic_compensation eta h0 h1).2.2]
  exact smul_ne_zero (by norm_num) hc

/-- Diagnostic of the exact VECTOR error after its first term is identified.
It neither changes the native source nor discards its residual. -/
def cubicPart (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) (k : ℕ) :=
  ((k:ℂ)+1)^2 • (normalizedPart eta h0 h1 c a k-
    (h 0:ℂ) • linearPart eta h0 h1 c a)

/-- The original native analytic tail remains an explicit physical vector. -/
theorem cubic_part_expansion (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) : ∀ᶠ k : ℕ in atTop,
      cubicPart eta h0 h1 c a k=
        (-(h 1:ℂ)) • cubicProfile eta h0 h1 c a+
        (radialStep k:ℂ)^2 • partField eta h0 h1 (remainderSamples 2 (radialStep k)) c a := by
  filter_upwards [normalized_part_expansion eta h0 h1 c a] with k hk
  unfold cubicPart
  rw [hk]
  have he : ((h 0:ℂ) • linearPart eta h0 h1 c a+
      (-(h 1:ℂ)*(radialStep k:ℂ)^2) • cubicProfile eta h0 h1 c a+
      (radialStep k:ℂ)^4 • partField eta h0 h1 (remainderSamples 2 (radialStep k)) c a)-
      (h 0:ℂ) • linearPart eta h0 h1 c a=
      (-(h 1:ℂ)*(radialStep k:ℂ)^2) • cubicProfile eta h0 h1 c a+
      (radialStep k:ℂ)^4 • partField eta h0 h1 (remainderSamples 2 (radialStep k)) c a := by module
  rw [he]
  simp only [smul_add,smul_smul]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hi2 := congrArg (fun z : ℂ => z^2) hi
  simp only [mul_pow,one_pow] at hi2
  have hB : ((k:ℂ)+1)^2*(-(h 1:ℂ)*(radialStep k:ℂ)^2)= -(h 1:ℂ) := by
    linear_combination -(h 1:ℂ)*hi2
  have hR : ((k:ℂ)+1)^2*(radialStep k:ℂ)^4=(radialStep k:ℂ)^2 := by
    linear_combination (radialStep k:ℂ)^2*hi2
  rw [hB,hR]

theorem cubic_part_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) : Tendsto (cubicPart eta h0 h1 c a) atTop
      (nhds ((-(h 1:ℂ)) • cubicProfile eta h0 h1 c a)) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (part_full_remainder_continuous 2 eta h0 h1 c a).tendsto.comp ht
  have hl := (tendsto_const_nhds (x:=(-(h 1:ℂ)) • cubicProfile eta h0 h1 c a)).add
    ((ht.pow 2).smul hR)
  simp only [zero_pow (by decide : 2≠0),zero_smul,add_zero] at hl
  apply hl.congr'
  filter_upwards [cubic_part_expansion eta h0 h1 c a] with k hk
  exact hk.symm

/-- The quarter is forced by the TWO original radial scales, not fitted. -/
theorem doubled_cubic_vector_identity (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) (k : ℕ) :
    ((k:ℂ)+1)^2 • (normalizedPart eta h0 h1 c a (2*k+1)-
      (h 0:ℂ) • linearPart eta h0 h1 c a)=
      (1/4:ℂ) • cubicPart eta h0 h1 c a (2*k+1) := by
  unfold cubicPart
  rw [smul_smul]
  congr 1
  push_cast
  ring

end
end CarryGreenCubic
