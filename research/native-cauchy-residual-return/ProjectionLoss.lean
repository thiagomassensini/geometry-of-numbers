import NativeTangent

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

def returnedHead (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical :=
  (nativeBoundaryProjection k).toLinearMap.comp (nativeOut k N)

/-- This candidate projects BOTH remaining channels. Its lost term is
computed below, rather than silently declared irrelevant. -/
def projectedBothPair (k N : ℕ) (c d : Fin N → ℂ) : ℂ :=
  inner ℂ (remainingIncident k N c) (remainingIncident k N d) -
    inner ℂ (nativeOut k N c-returnedHead k N c)
      (nativeOut k N d-returnedHead k N d)

theorem projection_loss_polarized (k N : ℕ) (c d : Fin N → ℂ) :
    projectedBothPair k N c d = remainingPair k N c d+
      inner ℂ (returnedHead k N c) (returnedHead k N d) := by
  have h := projection_split (nativeBoundarySpan k) (nativeOut k N c) (nativeOut k N d)
  change inner ℂ (nativeOut k N c) (nativeOut k N d) =
    inner ℂ (returnedHead k N c) (returnedHead k N d)+
      inner ℂ (nativeOut k N c-returnedHead k N c)
        (nativeOut k N d-returnedHead k N d) at h
  unfold projectedBothPair remainingPair
  rw [h]
  ring

theorem projection_loss_energy (k N : ℕ) (c : Fin N → ℂ) :
    (projectedBothPair k N c c).re = (remainingPair k N c c).re+‖returnedHead k N c‖^2 := by
  rw [projection_loss_polarized, Complex.add_re, physical_inner_self_re]

theorem returnedHead_basis (k N : ℕ) (i : Fin N) :
    returnedHead k N (Pi.single i 1) =
      (((2/((i.val:ℝ)+2):ℝ):ℂ)) • (returnedCoefficient k i • nativeAnchor k) := by
  change nativeBoundaryProjection k (nativeOut k N (Pi.single i 1)) = _
  rw [nativeOut_basis, map_smul, feature_projection]
  simp only [smul_smul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_natCast]
  congr 1
  ring

theorem nativeAnchor_norm_sq (k : ℕ) : ‖nativeAnchor k‖^2 = anchorMass k := by
  have h := congrArg Complex.re (nativeAnchor_inner k)
  simpa only [physical_inner_self_re, Complex.ofReal_re] using h

/-- This boundary loss is a literal original physical norm. -/
theorem returnedHead_energy (k N : ℕ) (i : Fin N) :
    ‖returnedHead k N (Pi.single i 1)‖^2 =
      2*((k:ℝ)+1)*Complex.normSq (returnedCoefficient k i)/((i.val:ℝ)+2)^2 := by
  rw [returnedHead_basis, norm_smul, norm_smul, mul_pow, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.normSq_eq_norm_sq,
    nativeAnchor_norm_sq]
  unfold anchorMass
  have hp : (i.val:ℝ)+2 ≠ 0 := by positivity
  field_simp

/-- In the natural Schur normalization of PR52 the omitted physical term
has a NONZERO limit. This uses only h0>0 and the actual return tangent. -/
theorem projection_loss_schur_tendsto (N : ℕ) (i : Fin N) :
    Tendsto (fun k => ‖returnedHead k N (Pi.single i 1)‖^2/oneDeficit k) atTop
      (nhds (4*canonicalCompletedNativeLogDerivativeMoment 0*(i.val:ℝ)^2/((i.val:ℝ)+2)^2)) := by
  have hb := Complex.continuous_normSq.continuousAt.tendsto.comp (returnedCoefficient_tangent i)
  have ht := ((hb.const_mul 2).div_const (((i.val:ℝ)+2)^2)).div central_deficit_tangent
    (mul_ne_zero (by norm_num : (8:ℝ) ≠ 0) canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne')
  have hl : (2*Complex.normSq (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(i.val:ℂ))/
      ((i.val:ℝ)+2)^2)/(8*canonicalCompletedNativeLogDerivativeMoment 0) =
      4*canonicalCompletedNativeLogDerivativeMoment 0*(i.val:ℝ)^2/((i.val:ℝ)+2)^2 := by
    have hm := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
    simp only [Complex.normSq_mul, Complex.normSq_natCast, Complex.normSq_ofNat,
      Complex.normSq_ofReal]
    field_simp
    ring
  rw [hl] at ht
  apply ht.congr'
  filter_upwards [oneDeficit_eventually_pos] with k hk
  change (2*Complex.normSq (returnedCoefficient k i*radialScale k)/((i.val:ℝ)+2)^2)/
    (oneDeficit k*((k:ℝ)+1)) = ‖returnedHead k N (Pi.single i 1)‖^2/oneDeficit k
  rw [returnedHead_energy]
  have hT : Complex.normSq (radialScale k) = ((k:ℝ)+1)^2 := by
    have he : radialScale k = (((k:ℝ)+1:ℝ):ℂ) := by simp [radialScale]
    rw [he, Complex.normSq_ofReal]
    ring
  rw [Complex.normSq_mul, hT]
  have hs : ((k:ℝ)+1) ≠ 0 := by positivity
  have hp : (i.val:ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem projection_loss_strict_eventually (N : ℕ) (i : Fin N) (hi : i.val ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      (remainingPair k N (Pi.single i 1) (Pi.single i 1)).re <
        (projectedBothPair k N (Pi.single i 1) (Pi.single i 1)).re := by
  have hl : 0 < 4*canonicalCompletedNativeLogDerivativeMoment 0*(i.val:ℝ)^2/((i.val:ℝ)+2)^2 := by
    have hi' : (i.val:ℝ) ≠ 0 := by exact_mod_cast hi
    exact div_pos (mul_pos (mul_pos (by norm_num) canonicalCompletedNativeLogDerivativeMoment_zero_pos)
      (sq_pos_of_ne_zero hi')) (sq_pos_of_pos (by positivity))
  have ht := (tendsto_order.mp (projection_loss_schur_tendsto N i)).1 0 hl
  filter_upwards [ht, oneDeficit_eventually_pos] with k hk hd
  have hn := (div_pos_iff.mp hk).resolve_right (by intro h; linarith [h.2])
  rw [projection_loss_energy]
  linarith [hn.1]

theorem second_source_projection_loss :
    Tendsto (fun k => ‖returnedHead k 2 (Pi.single 1 1)‖^2/oneDeficit k) atTop
      (nhds (4*canonicalCompletedNativeLogDerivativeMoment 0/9)) := by
  have h := projection_loss_schur_tendsto 2 (1 : Fin 2)
  norm_num at h
  exact h

end
end CarryCauchyResidual
