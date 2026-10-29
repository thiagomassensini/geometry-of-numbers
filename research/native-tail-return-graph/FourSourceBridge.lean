import PolarizedReturnDefect
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSampleStorage
namespace CarryTailReturn
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- A finite coefficient family stays nonzero under the ORIGINAL regular amplitude. -/
theorem weighted_coordinates_ne_zero (N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) (hne : x≠0) (hw : ∀ i : Fin N, w i≠0) :
    (fun i : Fin N => w i*x i)≠0 := by
  intro hz
  apply hne
  ext j
  by_cases hj : j<N
  · have he := congrFun hz ⟨j,hj⟩
    change w j*x j=0 at he
    exact (mul_eq_zero.mp he).resolve_left (hw ⟨j,hj⟩)
  · exact coefficient_outside_prefix x hx j (by omega)

theorem address_zero_input (p : ℕ) : addressPower p (0 : ℕ →₀ ℂ)=0 := by
  ext j
  simp [address_power_apply]

/-- Four literal coefficients of PR118, with the original imaginary phase. -/
theorem principal_coefficient_formula (a : ℝ) (k : ℕ) (i : Fin 4) :
    principalInput a k i = Complex.I*((((k:ℝ)+1)/6 *
      ![-(((k:ℝ)+1)^2+13*a),
        3*((k:ℝ)+1)^2+48*a,
        -(3*((k:ℝ)+1)^2)-63*a,
        ((k:ℝ)+1)^2+28*a] i : ℝ):ℂ) := by
  fin_cases i <;>
    norm_num [principalInput,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
      address_power_apply,native_odd_coefficient,nativeOddBeta] <;> ring

/-- Euclidean coefficient size ONLY: this is not the physical Cauchy metric. -/
theorem principal_coefficients_sq (a : ℝ) (k : ℕ) :
    (∑ i : Fin 4, Complex.normSq (principalInput a k i)) =
      ((k:ℝ)+1)^2*(3613*a^2+374*a*((k:ℝ)+1)^2+10*((k:ℝ)+1)^4)/18 := by
  simp only [principal_coefficient_formula]
  norm_num [Fin.sum_univ_succ,Complex.normSq,Complex.mul_re,Complex.mul_im,
    Complex.div_re,Complex.div_im]
  ring

/-- Exact completed square from the supplied symbolic certificate, now over
all real a and all actual radial indices in the Lean kernel. -/
theorem principal_coefficients_completed_square (a : ℝ) (k : ℕ) :
    (∑ i : Fin 4, Complex.normSq (principalInput a k i)) =
      (3613/18:ℝ)*((k:ℝ)+1)^2*(a+187*((k:ℝ)+1)^2/3613)^2+
        (129/7226:ℝ)*((k:ℝ)+1)^6 := by
  rw [principal_coefficients_sq]
  ring

theorem principal_coefficients_sq_pos (a : ℝ) (k : ℕ) :
    0 < ∑ i : Fin 4, Complex.normSq (principalInput a k i) := by
  rw [principal_coefficients_completed_square]
  positivity

/-- The original source cannot vanish, for any a or k. No moment sign input. -/
theorem principal_input_nonzero (a : ℝ) (k : ℕ) : principalInput a k≠0 := by
  intro hz
  have hp := principal_coefficients_sq_pos a k
  simp [hz] at hp

/-- FINITE CONTROL ONLY. Reuses the old four-source analytic source certificate;
no new quadrature or all-order sign claim is made. -/
theorem four_original_physical_positive :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ, x.support ⊆ Finset.range 4 → x≠0 →
      0<(canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x)
        (physicalCompletedFiniteSource k x)).re := by
  filter_upwards [storage_one_original_fourSample_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hp hreg
  intro x hx hne
  have hw (i : Fin 4) : incidentWeight k i≠0 :=
    completedNativeNormalizedPositiveChiralAmplitude_ne_zero (hreg i).2.1 (hreg i).2.2
  have hc := weighted_coordinates_ne_zero 4 (incidentWeight k) x hx hne hw
  have hs := hp (fun i : Fin 4 => incidentWeight k i*x i) hc
  rw [original_source_storage k 4 x hx] at hs
  linarith

/-- Both arguments of the actual projective source are carried to the existing
positive return-energy port. Contractivity is discharged by the OLD N=4 proof. -/
theorem four_original_port_gram :
    ∀ᶠ k : ℕ in atTop, ∀ x y : ℕ →₀ ℂ,
      x.support ⊆ Finset.range 4 → y.support ⊆ Finset.range 4 →
      inner ℂ (radialReturnEnergyPort k 4 (sourceIncident k 4 x))
        (radialReturnEnergyPort k 4 (sourceIncident k 4 y))=
          2*canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x)
            (physicalCompletedFiniteSource k y) := by
  filter_upwards [radialReturnTransfer_four_eventually_norm_le_one] with k hk
  intro x y hx hy
  exact original_source_port_pairing k 4 x y hx hy hk

/-- Regression requested by the notes, with all nine Green crossings and TWO
independent a,b. The sqrt(k+1) amplitude is not inserted a second time. -/
theorem principal_four_port_gram (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : ℝ,
      inner ℂ (radialReturnEnergyPort k 4 (sourceIncident k 4 (principalInput a k)))
        (radialReturnEnergyPort k 4 (sourceIncident k 4 (principalInput b k)))=
          2*crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k) := by
  filter_upwards [four_original_port_gram] with k hk
  intro a b
  rw [cross_green_eq_original]
  exact hk _ _ (principal_prefix a k 4 (by decide)) (principal_prefix b k 4 (by decide))

/-- This closes the FINITE principal sign test only, uniformly in a after k.
It is not an all-order result or a strict-limit argument. -/
theorem principal_four_eventually_positive (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      0<(crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput a k)).re := by
  filter_upwards [four_original_physical_positive] with k hk
  intro a
  rw [cross_green_eq_original]
  exact hk _ (principal_prefix a k 4 (by decide)) (principal_input_nonzero a k)

end
end CarryTailReturn
