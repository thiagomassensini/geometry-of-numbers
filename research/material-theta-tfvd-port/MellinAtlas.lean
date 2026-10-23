import PortTfvd
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import CPFormal.Analytic.CpNativeCarryFiniteCameraAlgebra
import NativeCarryC3Crosswalk.FinitePackaging

/-! Calibration to the original material waves, with complex spectral
parameter and the unmodified Gamma factor. The atlas identities are applied
to the entire three-channel port, before either Green projection. -/
namespace CarryMaterialTheta
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Camera NativeCarryC3Crosswalk
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def finiteHeatSynthesis (N : ℕ) (a : Fin N → ℂ) (x : ℝ) : ℂ :=
  ∑ i : Fin N, a i *
    (Real.exp (-Real.pi * ((i.val+1 : ℕ) : ℝ)^2 * x) : ℂ)

/-- The actual theta modes are the logarithmic change of variables of this
material heat synthesis, with the original exp(u/2) dressing. -/
theorem heat_to_theta_value (N : ℕ) (a : Fin N → ℂ) (u : ℝ) :
    (thetaLift N a u).1 =
      (Real.exp (u/2) : ℂ) * finiteHeatSynthesis N a (Real.exp (2*u)) := by
  simp only [thetaLift, resolvedThetaLift, materialThetaMode, Prod.fst_sum,
    addressMode, Complex.ofReal_mul, finiteHeatSynthesis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact finite Mellin calibration, retaining arbitrary complex coefficients
and their phases. This is an equality of readouts, not an L2 isometry. -/
theorem finite_heat_mellin (N : ℕ) (a : Fin N → ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (finiteHeatSynthesis N a) (s/2) =
      Complex.Gammaℝ s * ∑ i : Fin N, a i / ((i.val+1 : ℕ) : ℂ)^s := by
  have hF : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasSum (fun i : Fin N =>
        if ((i.val+1 : ℕ) : ℝ) = 0 then 0 else
          a i * (Real.exp (-Real.pi * ((i.val+1 : ℕ) : ℝ)^2 * x) : ℂ))
        (finiteHeatSynthesis N a x) := by
    intro x _
    have hz (i : Fin N) : ((i.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
    simpa only [finiteHeatSynthesis, hz, if_false] using
      hasSum_fintype (fun i : Fin N =>
        a i * (Real.exp (-Real.pi * ((i.val+1 : ℕ) : ℝ)^2 * x) : ℂ))
  have h := hasSum_mellin_pi_mul_sq hs hF (hasSum_fintype _).summable
  have habs (i : Fin N) :
      ((|((i.val+1 : ℕ) : ℝ)| : ℝ) : ℂ) = ((i.val+1 : ℕ) : ℂ) := by
    rw [abs_of_nonneg (by positivity)]
    norm_cast
  simpa only [tsum_fintype, habs, Finset.mul_sum, mul_div_assoc] using h.tsum_eq.symm

/-- On the native real-height axis the calibration recovers the actual
upstream two-quadrature material samples, not prescribed zeros or moments. -/
theorem finite_heat_mellin_native (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    mellin (finiteHeatSynthesis N a) (nativeLine t / 2) =
      Complex.Gammaℝ (nativeLine t) *
        ∑ i : Fin N, a i *
          nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState t (i.val+1)) := by
  rw [finite_heat_mellin N a (by simp [nativeLine])]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [packaged_nativeState_eq_dirichletValue_nativeLine]
  simp only [dirichletValue, Complex.cpow_neg, div_eq_mul_inv]

/-- Integer address wrapper only. The original odd chart evaluates strictly
positive addresses; n=0 is not introduced as a physical source. -/
def integerThetaPort (f : ℤ → ℂ) (n : ℤ) (u : ℝ) : MaterialThetaPort :=
  materialThetaMode n.toNat (f n) u

theorem odd_camera_port_normal_form (b M : ℕ) (hodd : Odd b) (hb : 1 < b)
    (f : ℤ → ℂ) :
    nativeCarryFiniteSaturatedChart b M (integerThetaPort f) =
      nativeCarryPositivePrefix
        ((b : ℤ)*(M : ℤ)+(CPFormal.Genuine.Cp.halfRange b : ℤ))
        (integerThetaPort f) -
      b • nativeCarryCenterChannel b M (integerThetaPort f) :=
  nativeCarryFiniteSaturatedChart_odd_normal_form b M hodd hb _

/-- Both decompositions of a product camera retain all three channels and
the original cutoff adjustments. In particular b=9 requires no prime input. -/
theorem odd_atlas_port_cross_identity (a b M : ℕ)
    (haodd : Odd a) (hbodd : Odd b) (ha : 1 < a) (hb : 1 < b)
    (f : ℤ → ℂ) :
    nativeCarryFiniteSaturatedChart a
        (b*M+CPFormal.Genuine.Cp.halfRange b) (integerThetaPort f) +
      a • nativeCarryFiniteSaturatedChart b M
        (fun n => integerThetaPort f ((a : ℤ)*n)) =
    nativeCarryFiniteSaturatedChart b
        (a*M+CPFormal.Genuine.Cp.halfRange a) (integerThetaPort f) +
      b • nativeCarryFiniteSaturatedChart a M
        (fun n => integerThetaPort f ((b : ℤ)*n)) :=
  nativeCarryFiniteSaturatedChart_odd_cross_identity a b M haodd hbodd ha hb _

/-- The full synthesized Green pairing contains every ordered pair of
addresses. It is not a diagonal sum of material masses. -/
theorem theta_lift_green_all_crosses (N M : ℕ) (a : Fin N → ℂ)
    (d : Fin M → ℂ) (u v : ℝ) :
    NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
      (logPort (thetaLift N a u)) (logPort (thetaLift M d v)) =
      ∑ i : Fin N, ∑ j : Fin M,
        NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
          (logPort (resolvedThetaLift N a u i))
          (logPort (resolvedThetaLift M d v j)) := by
  simp only [thetaLift, logPort, Prod.fst_sum, Prod.snd_sum,
    NativeCarrySpectralWeyl.Boundary.greenForm, sum_inner, inner_sum,
    Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

end
end CarryMaterialTheta
