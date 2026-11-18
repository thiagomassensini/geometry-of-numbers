import DampedCamera
import StencilObstruction
import CarrySelfAdjointOperator.CompletedNativeAmbientRadialIntertwiningNoGo
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort

/-! The variable defect left by the exact overlap recombination, with the
same characteristic normalization and both native parameter slots. -/

namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport CarryTraceFiber ChiralReturn CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false

/-- Its weights are forced by the native positive chiral amplitude. -/
def normalizedDefectEntry (k N : ℕ) (hs : strip k N) (i j : Fin N) : ℂ :=
  conj (canonicalCompletedC3FullWronskianChiralNormalization (radialPoint k i)) *
    canonicalCompletedC3FullWronskianChiralNormalization (radialPoint k j) *
      (inner ℂ (radialField k i) (radialField k j) *
        defectPair (radialPoint k i) (radialPoint k j)
          (nativeSource (radialPoint k i) (hs i)) (nativeSource (radialPoint k j) (hs j)))

def normalizedDampedEntry (k N : ℕ) (hs : strip k N) (i j : Fin N) : ℂ :=
  radialOverlap k i j * canonicalCompletedC3NormalizedAmbientResponseKernel
    (radialPoint k i) (radialPoint k j) (hs i).1 (hs j).1

private theorem normalization_mul (z w : ℂ) :
    conj (canonicalCompletedC3FullWronskianChiralNormalization z) *
      canonicalCompletedC3FullWronskianChiralNormalization w =
    (canonicalCompletedC3GammaCharacteristicWeight z w)⁻¹ := by
  unfold canonicalCompletedC3FullWronskianChiralNormalization
    canonicalCompletedC3GammaCharacteristicWeight
  rw [map_inv₀, map_mul, Complex.conj_ofReal, ← mul_inv]
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  congr 1
  linear_combination (conj (completedNativeOperatorCharacteristic z) *
    completedNativeOperatorCharacteristic w) * hsq

/-- The same trace and fiber from the enriched TFVD state with both slots kept. -/
theorem normalizedDefectEntry_eq_signed_trace_sub_fiber (k N : ℕ)
    (hs : strip k N) (i j : Fin N) :
    normalizedDefectEntry k N hs i j =
      conj (canonicalCompletedC3FullWronskianChiralNormalization (radialPoint k i)) *
        canonicalCompletedC3FullWronskianChiralNormalization (radialPoint k j) *
        (inner ℂ (radialField k i) (radialField k j) *
          signaturePair (radialPoint k i) (radialPoint k j)
            (tracePart (nativeSource (radialPoint k i) (hs i)))
            (tracePart (nativeSource (radialPoint k j) (hs j)))) -
          normalizedDampedEntry k N hs i j := by
  unfold normalizedDefectEntry normalizedDampedEntry
  rw [defectPair_signature, ← signature_trace]
  have hAmbient : inner ℂ (ambientReadout (nativeSource (radialPoint k i) (hs i)))
      (ambientReadout (nativeSource (radialPoint k j) (hs j))) =
      canonicalCompletedC3AmbientResponseKernel (radialPoint k i) (radialPoint k j)
        (hs i).1 (hs j).1 := by
    rw [← ambient_fiber (nativeSource (radialPoint k i) (hs i)),
      ← ambient_fiber (nativeSource (radialPoint k j) (hs j))]
    exact ambientMatrix_eq_kernel k N hs i j
  rw [hAmbient, normalization_mul]
  unfold radialOverlap canonicalCompletedC3NormalizedAmbientResponseKernel
  ring

/-- Signed exact relation to the original Wronskian. There is no
positivity or smallness hypothesis on the defect. -/
theorem normalizedDefectEntry_eq_dslope_sub_damped (k N : ℕ)
    (hs : strip k N) (i j : Fin N)
    (hi : completedNativeOperatorCharacteristic (radialPoint k i) ≠ 0)
    (hj : completedNativeOperatorCharacteristic (radialPoint k j) ≠ 0) :
    normalizedDefectEntry k N hs i j =
      canonicalCompletedNativePolarizedDslopeKernel (radialPoint k i) (radialPoint k j) -
        normalizedDampedEntry k N hs i j := by
  rw [normalizedDefectEntry_eq_signed_trace_sub_fiber, normalization_mul]
  congr 1
  let z := radialPoint k i
  let w := radialPoint k j
  let C := inner ℂ (radialField k i) (radialField k j)
  let T := signaturePair z w (tracePart (nativeSource z (hs i))) (tracePart (nativeSource w (hs j)))
  let wt := canonicalCompletedC3GammaCharacteristicWeight z w
  let Q := canonicalCompletedNativePolarizedDslopeKernel z w
  change wt⁻¹ * (C * T) = Q
  have hsep : w - conj z ≠ 0 := canonicalCompletedC3RadialTilt_separation_ne_zero k i j
  have ht : Complex.I * T = wt * ((w - conj z) * Q) :=
    native_kernel_trace_signature z w (hs i) (hs j) hi hj (sub_ne_zero.mp hsep)
  have hwt : wt ≠ 0 := by
    unfold wt canonicalCompletedC3GammaCharacteristicWeight
    exact mul_ne_zero (mul_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).2 hi)) hj
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    _ = C * (Complex.I * T) / wt := by ring
    _ = C * (wt * ((w - conj z) * Q)) / wt := by rw [ht]
    _ = C * ((w - conj z) * Q) := by field_simp
    _ = _ := by rw [← mul_assoc, radialCauchy_inner_mul_separation]

/-- Match the published ambient grid to a cofinal subsequence of the
original projective radial grid, without changing the points. -/
def commonIndex (N k : ℕ) : ℕ := 2 * (N + 1) * (k + 1) - 1

private theorem commonIndex_succ (N k : ℕ) :
    commonIndex N k + 1 = 2 * (N + 1) * (k + 1) := by
  unfold commonIndex
  have hpos : 0 < 2 * (N + 1) * (k + 1) := Nat.mul_pos (by omega) (Nat.succ_pos k)
  exact Nat.sub_add_cancel (by omega)

theorem commonIndex_tendsto (N : ℕ) : Tendsto (commonIndex N) atTop atTop := by
  apply tendsto_atTop_mono (f := fun k : ℕ => k) _ tendsto_id
  intro k
  have h := commonIndex_succ N k
  have hle : k + 1 ≤ 2 * (N + 1) * (k + 1) := by
    calc
      _ = 1 * (k + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  omega

theorem commonPoint_eq (N k : ℕ) (i : Fin N) :
    radialPoint (commonIndex N k) i = canonicalCompletedC3AmbientRadialTiltPoint k N i := by
  apply Complex.ext
  · simp [radialPoint, canonicalCompletedC3RadialTiltPoint, canonicalCompletedC3RadialTiltStep,
      canonicalGreenJetStep]
  · rw [canonicalCompletedC3RadialTiltPoint_im, canonicalCompletedC3AmbientRadialTiltPoint_im]
    unfold canonicalCompletedC3AmbientRadialTiltScale
    push_cast
    rw [show ((commonIndex N k : ℝ) + 1) =
      (2 : ℝ) * ((N : ℝ) + 1) * ((k : ℝ) + 1) by exact_mod_cast commonIndex_succ N k]

theorem commonStrip (N k : ℕ) : strip (commonIndex N k) N := by
  intro i
  rw [commonPoint_eq]
  constructor
  · exact canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i
  · have h := canonicalCompletedC3AmbientRadialTiltPoint_im_pos k N i
    norm_num [operatorHeightParameter, Complex.mul_re] at *
    linarith

def ambientCenterEnergy : ℝ :=
  ‖canonicalCompletedC3NormalizedAmbientResponseState 0
    (by norm_num [operatorHeightParameter])‖ ^ 2

theorem ambientCenterEnergy_pos : 0 < ambientCenterEnergy := by
  have h := canonicalCompletedC3NormalizedAmbientCentralExcess_pos
  change 0 < ambientCenterEnergy - canonicalCompletedNativeLogDerivativeMoment 0 at h
  linarith [canonicalCompletedNativeLogDerivativeMoment_zero_pos]

private theorem ambientKernel_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => canonicalCompletedC3NormalizedAmbientResponseKernel
      (canonicalCompletedC3AmbientRadialTiltPoint k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint k N j)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
      (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j)) atTop
      (nhds (ambientCenterEnergy : ℂ)) := by
  have h := canonicalCompletedC3NormalizedAmbientResponseKernel_ambientRadial_tendsto N i j
  unfold ambientCenterEnergy
  rw [Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq_to_K] at h
  exact h

theorem normalizedDampedEntry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => normalizedDampedEntry (commonIndex N k) N (commonStrip N k) i j)
      atTop (nhds (radialOverlap 0 i j * (ambientCenterEnergy : ℂ))) := by
  apply ((ambientKernel_tendsto N i j).const_mul (radialOverlap 0 i j)).congr'
  filter_upwards with k
  unfold normalizedDampedEntry
  rw [radialOverlap_independent (commonIndex N k) 0]
  congr 1
  congr 1
  · exact (commonPoint_eq N k i).symm
  · exact (commonPoint_eq N k j).symm

theorem dslopeEntry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => canonicalCompletedNativePolarizedDslopeKernel
      (radialPoint (commonIndex N k) i) (radialPoint (commonIndex N k) j))
      atTop (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have h := (ambientKernel_tendsto N i j).sub
    (canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess N i j)
  have hcentral : (ambientCenterEnergy : ℂ) - (canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    change (ambientCenterEnergy : ℂ) - ((ambientCenterEnergy -
      canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) = _
    rw [Complex.ofReal_sub]
    ring
  rw [hcentral] at h
  apply h.congr'
  filter_upwards with k
  simp only [canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub, commonPoint_eq]
  ring

theorem normalizedDefectEntry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => normalizedDefectEntry (commonIndex N k) N (commonStrip N k) i j)
      atTop (nhds ((canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
        radialOverlap 0 i j * (ambientCenterEnergy : ℂ))) := by
  apply ((dslopeEntry_tendsto N i j).sub (normalizedDampedEntry_tendsto N i j)).congr'
  filter_upwards [(commonIndex_tendsto N).eventually
    (canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N)] with k hk
  exact (normalizedDefectEntry_eq_dslope_sub_damped (commonIndex N k) N
    (commonStrip N k) i j (hk i).2.1 (hk j).2.1).symm

/-- The original source coefficients after applying its own chiral
amplitude, as in the native normalized difference jets. -/
def normalizedInput (k : ℕ) {N : ℕ} (x : Fin N → ℂ) : Fin N → ℂ :=
  fun i => x i * completedNativeNormalizedPositiveChiralAmplitude (radialPoint k i)

private theorem normalizedInput_sourceWeight (k : ℕ) {N : ℕ}
    (x : Fin N → ℂ) (i : Fin N)
    (hi : completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i) ≠ 0) :
    sourceWeight k (normalizedInput k x) i =
      x i * canonicalCompletedC3FullWronskianChiralNormalization (radialPoint k i) := by
  unfold sourceWeight normalizedInput completedNativeNormalizedPositiveChiralAmplitude
  rw [← mul_assoc, mul_div_cancel_right₀ _ hi]

def pairing {N : ℕ} (K : Fin N → Fin N → ℂ) (x y : Fin N → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (x i) * y j * K i j

theorem normalizedSourceBalance_eq_damped_add_defect (k : ℕ) {N : ℕ}
    (x y : Fin N → ℂ) (hs : strip k N)
    (hp : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i) ≠ 0) :
    polarizedSourceBalance k (normalizedInput k x) (normalizedInput k y) 1 1 =
      2 * (pairing (normalizedDampedEntry k N hs) x y +
        pairing (normalizedDefectEntry k N hs) x y) := by
  rw [source_balance_budget _ _ _ hs]
  have hcam := camera_sub_overlap_eq_damped k (normalizedInput k x) (normalizedInput k y) hs
  have hd : dampedCameraBalance k (normalizedInput k x) (normalizedInput k y) hs =
      pairing (normalizedDampedEntry k N hs) x y := by
    unfold dampedCameraBalance pairing
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [normalizedInput_sourceWeight k x i (hp i),
      normalizedInput_sourceWeight k y j (hp j), map_mul, dampedCameraMatrix,
      Matrix.hadamard_apply, overlapMatrix, ambientMatrix_eq_kernel,
      normalizedDampedEntry, canonicalCompletedC3NormalizedAmbientResponseKernel,
      div_eq_mul_inv]
    rw [← normalization_mul]
    ring
  have hv : variableDefect k (normalizedInput k x) (normalizedInput k y) hs =
      pairing (normalizedDefectEntry k N hs) x y := by
    unfold variableDefect pairing
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [normalizedInput_sourceWeight k x i (hp i),
      normalizedInput_sourceWeight k y j (hp j), map_mul, normalizedDefectEntry]
    ring
  linear_combination 2 * hcam + 2 * hd + 2 * hv

private theorem pairing_tendsto {N : ℕ} (x y : Fin N → ℂ)
    {K : ℕ → Fin N → Fin N → ℂ} {T : Fin N → Fin N → ℂ}
    (h : ∀ i j, Tendsto (fun k => K k i j) atTop (nhds (T i j))) :
    Tendsto (fun k => pairing (K k) x y) atTop (nhds (pairing T x y)) := by
  unfold pairing
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (h i j).const_mul (conj (x i) * y j)

private theorem pairing_const_balanced {N : ℕ} (x : Fin N → ℂ) (a : ℂ)
    (h : ∑ i, x i = 0) : pairing (fun _ _ => a) x x = 0 := by
  unfold pairing
  have hz (i : Fin N) : (∑ j, conj (x i) * x j * a) = 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul, h, zero_mul, mul_zero]
  simp only [hz, Finset.sum_const_zero]

private theorem pairing_overlap_scaled {N : ℕ} (x : Fin N → ℂ) :
    pairing (fun i j => radialOverlap 0 i j * (ambientCenterEnergy : ℂ)) x x =
      ((ambientCenterEnergy * ‖observedSynthesis 0 x‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairing
  simp_rw [← mul_assoc]
  simp_rw [← Finset.sum_mul]
  rw [← observedSynthesis_pairing, inner_self_eq_norm_sq_to_K, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_comm]
  rfl

/-- For every fixed, nontrivial balanced input the variable source defect
uses all of the leading damped Gram. No uniform fractional slack remains
on these directions as the original radial mesh collapses. -/
theorem balanced_defect_ratio_tendsto_one {N : ℕ} (x : Fin N → ℂ)
    (hsum : ∑ i, x i = 0) (hx : x ≠ 0) :
    Tendsto (fun k : ℕ =>
      -(pairing (normalizedDefectEntry (commonIndex N k) N (commonStrip N k)) x x).re /
        (pairing (normalizedDampedEntry (commonIndex N k) N (commonStrip N k)) x x).re)
      atTop (nhds 1) := by
  let L := ambientCenterEnergy * ‖observedSynthesis 0 x‖ ^ 2
  have hS : observedSynthesis 0 x ≠ 0 := by
    intro he
    exact hx ((observedSynthesis_eq_zero_iff 0 x).mp he)
  have hL : 0 < L := mul_pos ambientCenterEnergy_pos (sq_pos_of_pos (norm_pos_iff.mpr hS))
  have hp := pairing_tendsto x x (normalizedDampedEntry_tendsto N)
  have hd := pairing_tendsto x x (normalizedDefectEntry_tendsto N)
  rw [pairing_overlap_scaled] at hp
  have hdiff : pairing
      (fun i j : Fin N => (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
        radialOverlap 0 i j * (ambientCenterEnergy : ℂ)) x x = -(L : ℂ) := by
    have he : pairing
        (fun i j : Fin N => (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
          radialOverlap 0 i j * (ambientCenterEnergy : ℂ)) x x =
        pairing (fun _ _ => (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) x x -
          pairing (fun i j => radialOverlap 0 i j * (ambientCenterEnergy : ℂ)) x x := by
      unfold pairing
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [he, pairing_const_balanced x _ hsum, pairing_overlap_scaled, zero_sub]
  rw [hdiff] at hd
  have hpr := Complex.continuous_re.continuousAt.tendsto.comp hp
  have hdr := Complex.continuous_re.continuousAt.tendsto.comp hd.neg
  simp only [Function.comp_def, Complex.ofReal_re, neg_neg] at hpr hdr
  have hq := hdr.div hpr hL.ne'
  change Tendsto _ atTop (nhds (L / L)) at hq
  rw [div_self hL.ne'] at hq
  refine hq.congr' ?_
  filter_upwards with k
  simp

#print axioms normalizedDefectEntry_eq_signed_trace_sub_fiber
#print axioms normalizedSourceBalance_eq_damped_add_defect
#print axioms normalizedDefectEntry_tendsto
#print axioms balanced_defect_ratio_tendsto_one

#print axioms normalizedDefectEntry_eq_dslope_sub_damped
#print axioms normalizedDampedEntry_tendsto

end
end CarryJetOverlap
