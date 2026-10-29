import CurvePairing

namespace CarryMovingRadial
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The normalized amplitude is part of the original state, not a constant
external to the radial flow. Its complete polarized defect is linear in Q. -/
theorem amplitude_defect (z w : ℂ)
    (hzF : completedNativeOperatorCharacteristic z≠0)
    (hwF : completedNativeOperatorCharacteristic w≠0)
    (hzP : completedNativePositiveHermiteBiehlerCoordinate z≠0)
    (hwP : completedNativePositiveHermiteBiehlerCoordinate w≠0) :
    conj (completedNativeNormalizedPositiveChiralAmplitude z)*
        completedNativeNormalizedPositiveChiralAmplitude w*
        (1-conj (completedNativeHermiteBiehlerChiralQuotient z)*
          completedNativeHermiteBiehlerChiralQuotient w)=
      Complex.I*(conj (completedNativeOperatorLogDerivative z)-
        completedNativeOperatorLogDerivative w) := by
  have he : ∀ a b q r : ℂ, conj a*b*(1-conj q*r)=conj a*b-conj (a*q)*(b*r) := by
    intro a b q r; simp only [map_mul]; ring
  rw [he,original_returned_amplitude z hzF hzP,original_returned_amplitude w hwF hwP,
    original_amplitude z hzF,original_amplitude w hwF]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hn : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  simp only [map_div₀,map_add,map_sub,Complex.conj_I,Complex.conj_ofReal]
  field_simp [hn]
  linear_combination -(Complex.I*(conj (completedNativeOperatorLogDerivative z)-
    completedNativeOperatorLogDerivative w))*hs

def rho (h : ℝ) (r : ℕ) : ℂ :=
  CarryCriticalTfvd.responseReadout (((r:ℂ)+1)*(h:ℂ))

theorem rho_real (h : ℝ) (r : ℕ) : conj (rho h r)=rho h r := by
  have he := CarryMixedParity.response_real_ray (((r:ℝ)+1)*h)
  simpa only [rho,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,
    Complex.ofReal_one] using he

theorem radial_amplitude_defect (h : ℝ) (i j : ℕ)
    (hiF : completedNativeOperatorCharacteristic (point h i)≠0)
    (hjF : completedNativeOperatorCharacteristic (point h j)≠0)
    (hiP : completedNativePositiveHermiteBiehlerCoordinate (point h i)≠0)
    (hjP : completedNativePositiveHermiteBiehlerCoordinate (point h j)≠0) :
    conj (completedNativeNormalizedPositiveChiralAmplitude (point h i))*
        completedNativeNormalizedPositiveChiralAmplitude (point h j)*
        (1-conj (curveQuotient h i)*curveQuotient h j)=2*(rho h i+rho h j) := by
  rw [curveQuotient,curveQuotient,amplitude_defect _ _ hiF hjF hiP hjP]
  have hq (r : ℕ) : completedNativeOperatorLogDerivative (point h r)=2*Complex.I*rho h r := by
    simpa only [point,rho,mul_assoc] using
      CarryRadialFlow.original_rotated_response (((r:ℂ)+1)*(h:ℂ))
  rw [hq i,hq j]
  simp only [map_mul,map_ofNat,Complex.conj_I,rho_real]
  ring_nf
  norm_num [Complex.I_sq]

theorem scale_product (h : ℝ) (hh : 0≤h) : conj (scale h)*scale h=(h:ℂ)⁻¹ := by
  simp only [scale,Complex.conj_ofReal]
  rw [← pow_two,← Complex.ofReal_pow,Real.sq_sqrt (inv_nonneg.mpr hh),Complex.ofReal_inv]

def responsePair (N : ℕ) (h : ℝ) (x y : Fin N → ℂ) : ℂ :=
  (2/(h:ℂ))*∑ i : Fin N, ∑ j : Fin N,
    conj (x i)*y j*(rho h i+rho h j)/((i:ℂ)+(j:ℂ)+2)

/-- All finite dimensions: completion and both return factors cancel only
inside the FULL polarized source kernel. The original h-dependent scale stays. -/
theorem fullPair_eq_response (N : ℕ) (h : ℝ) (hh : 0≤h) (x y : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point h i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point h i)≠0) :
    fullPair N (fun i => curveQuotient h i) (curveCoefficients N h x)
      (curveCoefficients N h y)=responsePair N h x y := by
  unfold fullPair responsePair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [curveCoefficients,map_mul]
  calc
    _ = conj (x i)*y j*(conj (scale h)*scale h)*
        (conj (completedNativeNormalizedPositiveChiralAmplitude (point h i))*
          completedNativeNormalizedPositiveChiralAmplitude (point h j)*
            (1-conj (curveQuotient h i)*curveQuotient h j))/((i:ℂ)+(j:ℂ)+2) := by ring
    _ = _ := by
      rw [scale_product h hh,radial_amplitude_defect h i j (hF i) (hF j) (hP i) (hP j)]
      ring

theorem physical_response_pair (N k : ℕ) (x y : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N (radialFourSourceStep k) x)
      (curveState N (radialFourSourceStep k) y)=
        responsePair N (radialFourSourceStep k) x y := by
  rw [curve_full_pair,fullPair_eq_response N _ (by unfold radialFourSourceStep; positivity)]
  · intro i; rw [point_at_grid]; exact hF i
  · intro i; rw [point_at_grid]; exact hP i

end
end CarryMovingRadial
