import SeparationCorrection
import CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewing

/-! The correction is carried by the ORIGINAL radial Cauchy features.
The diagonal scales are those already present in the native consumer.
No physical coefficient, source or carrier is replaced. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section

abbrev radialPoint := canonicalCompletedC3RadialTiltPoint
abbrev radialField := completedNativeRadialChiralCauchyState

/-- A bookkeeping overlap of the existing Cauchy vectors, using the fixed
consumer scales. The unscaled source remains unchanged. -/
def radialOverlap (k i j : ℕ) : ℂ :=
  Complex.ofReal (Real.sqrt (2*(radialPoint k i).im)*Real.sqrt (2*(radialPoint k j).im))*
    inner ℂ (radialField k i) (radialField k j)

theorem radialOverlap_inner (k i j : ℕ) :
    radialOverlap k i j=inner ℂ
      ((Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i)
      ((Real.sqrt (2*(radialPoint k j).im) : ℂ) • radialField k j) := by
  rw [inner_smul_left,inner_smul_right]
  simp only [radialOverlap,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

/-- Exact Cauchy transport of the two-argument scale correction. -/
theorem radial_cauchy_separation_correction (k i j : ℕ) :
    inner ℂ (radialField k i) (radialField k j)*
      separationCorrection (radialPoint k i) (radialPoint k j)=
        Complex.I*(1-radialOverlap k i j) := by
  have h := radialCauchy_inner_mul_separation k i j
  unfold separationCorrection radialOverlap
  linear_combination h

theorem radialOverlap_diagonal (k i : ℕ) : radialOverlap k i i=1 := by
  have h := radial_cauchy_separation_correction k i i
  rw [separationCorrection_diagonal _ (canonicalCompletedC3RadialTiltPoint_im_pos k i).le,
    mul_zero] at h
  have hh : 1-radialOverlap k i i=0 :=
    (mul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  exact (sub_eq_zero.mp hh).symm

/-- Same native unit vectors in the SAME Cauchy Hilbert, merely observed in
coordinates determined by the consumer diagonal scale. -/
theorem radial_observed_norm_sq (k i : ℕ) :
    ‖(Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i‖^2=1 := by
  have h : inner ℂ
      ((Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i)
      ((Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i)=1 := by
    rw [← radialOverlap_inner,radialOverlap_diagonal]
  calc
    _ = (inner ℂ
      ((Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i)
      ((Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = 1 := by rw [h]; rfl

/-- The ORIGINAL four-channel residual after its ORIGINAL Cauchy transport.
The full scale-overlap term and both native parameter slots remain present. -/
theorem radial_four_channel_overlap_identity (k i j : ℕ)
    (hi : operatorHeightParameter (radialPoint k i) ∈ genuineCriticalStrip)
    (hj : operatorHeightParameter (radialPoint k j) ∈ genuineCriticalStrip) :
    inner ℂ (radialField k i) (radialField k j)*
      canonicalCompletedC3CoisometricWronskianFourChannelDefect
        (radialPoint k i) (radialPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) hi.1 hj.1 =
      -Complex.I*inner ℂ (radialField k i) (radialField k j)*
        defectPair (radialPoint k i) (radialPoint k j)
          (nativeSource (radialPoint k i) hi) (nativeSource (radialPoint k j) hj)+
      Complex.I*(1-radialOverlap k i j)*inner ℂ
        (ambientReadout (fiberPart (nativeSource (radialPoint k i) hi)))
        (ambientReadout (fiberPart (nativeSource (radialPoint k j) hj))) := by
  rw [native_four_channel_separation_correction _ _
    (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
    (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) hi hj,mul_add]
  rw [← mul_assoc (inner ℂ (radialField k i) (radialField k j))
    (separationCorrection (radialPoint k i) (radialPoint k j)),
    radial_cauchy_separation_correction]
  ring


/-- Independent coefficient families, unequal finite dimensions, every
ordered cross. The original native source weights can be substituted as-is. -/
theorem finite_radial_overlap_transport (k : ℕ) {N M : ℕ}
    (beta : Fin N → ℂ) (gamma : Fin M → ℂ)
    (hi : ∀ i : Fin N, operatorHeightParameter (radialPoint k i) ∈ genuineCriticalStrip)
    (hj : ∀ j : Fin M, operatorHeightParameter (radialPoint k j) ∈ genuineCriticalStrip) :
    (∑ i, ∑ j, conj (beta i)*gamma j*(inner ℂ (radialField k i) (radialField k j)*
      canonicalCompletedC3CoisometricWronskianFourChannelDefect
        (radialPoint k i) (radialPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) (hi i).1 (hj j).1)) =
    ∑ i, ∑ j, conj (beta i)*gamma j*(
      -Complex.I*inner ℂ (radialField k i) (radialField k j)*
        defectPair (radialPoint k i) (radialPoint k j)
          (nativeSource (radialPoint k i) (hi i)) (nativeSource (radialPoint k j) (hj j))+
      Complex.I*(1-radialOverlap k i j)*inner ℂ
        (ambientReadout (fiberPart (nativeSource (radialPoint k i) (hi i))))
        (ambientReadout (fiberPart (nativeSource (radialPoint k j) (hj j))))) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [radial_four_channel_overlap_identity k i j (hi i) (hj j)]

end
end CarryFiberTransport
