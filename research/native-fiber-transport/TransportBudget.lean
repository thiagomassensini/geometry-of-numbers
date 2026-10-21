import CoherentSplit

/-! Exact images, both ordered crosses, and the signed defect of the native
camera/chiral consumer. No image is postulated to be contractive. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp
open scoped InnerProductSpace ComplexConjugate
noncomputable section

/-- The ORIGINAL enlarged map: ambient Naimark output and negative chirality. -/
theorem enlarged_trace (z : ℂ) (u : Source) :
    enlargedReadout z (tracePart u)=WithLp.toLp 2 (0,minusReadout z u) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change ((Real.sqrt (2*z.im) : ℝ) : ℂ) • ambientReadout (tracePart u)=0
    rw [ambient_trace_zero,smul_zero]
  · exact minus_trace _ _

theorem enlarged_fiber (z : ℂ) (u : Source) :
    enlargedReadout z (fiberPart u)=
      WithLp.toLp 2 ((((Real.sqrt (2*z.im) : ℝ) : ℂ) • ambientReadout u),0) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change ((Real.sqrt (2*z.im) : ℝ) : ℂ) • ambientReadout (fiberPart u)=_
    rw [ambient_fiber]
  · exact minus_fiber_zero _ _

/-- Real camera transport has the SAME split, on its exact existing carrier. -/
theorem camera_chiral_trace (z : ℂ) (u : Source) :
    canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z (tracePart u)=
      WithLp.toLp 2 (0,minusReadout z u) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change Real.sqrt (2*z.im) • cameraReadout (tracePart u)=0
    rw [camera_trace_zero,smul_zero]
  · exact minus_trace _ _

theorem camera_chiral_fiber (z : ℂ) (u : Source) :
    canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z (fiberPart u)=
      WithLp.toLp 2 (Real.sqrt (2*z.im) • cameraReadout u,0) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change Real.sqrt (2*z.im) • cameraReadout (fiberPart u)=_
    rw [camera_fiber]
  · exact minus_fiber_zero _ _

/-- Crosses vanish because their exact transported coordinate blocks differ.
The spectral slots z,w and the source slots u,v remain independent. -/
theorem enlarged_trace_fiber_cross (z w : ℂ) (u v : Source) :
    inner ℂ (enlargedReadout z (tracePart u)) (enlargedReadout w (fiberPart v))=0 := by
  rw [enlarged_trace,enlarged_fiber,WithLp.prod_inner_apply]
  simp

theorem enlarged_fiber_trace_cross (z w : ℂ) (u v : Source) :
    inner ℂ (enlargedReadout z (fiberPart u)) (enlargedReadout w (tracePart v))=0 := by
  rw [enlarged_trace,enlarged_fiber,WithLp.prod_inner_apply]
  simp

/-- Four-coordinate expansion in the ORIGINAL output metric. -/
theorem enlarged_pairing_split (z w : ℂ) (u v : Source) :
    inner ℂ (enlargedReadout z u) (enlargedReadout w v)=
      inner ℂ (enlargedReadout z (tracePart u)) (enlargedReadout w (tracePart v))+
        inner ℂ (enlargedReadout z (fiberPart u)) (enlargedReadout w (fiberPart v)) := by
  have hz := congrArg (enlargedReadout z) (source_reconstruction u)
  have hw := congrArg (enlargedReadout w) (source_reconstruction v)
  rw [map_add] at hz hw
  conv_lhs => rw [← hz,← hw]
  rw [inner_add_left,inner_add_right,inner_add_right,
    enlarged_trace_fiber_cross,enlarged_fiber_trace_cross]
  ring

/-- Bookkeeping for the EXISTING signed defect, not a new physical metric. -/
def defectPair (z w : ℂ) (u v : Source) : ℂ :=
  inner ℂ (plusReadout z u) (plusReadout w v)-
    inner ℂ (enlargedReadout z u) (enlargedReadout w v)

def defectEnergy (z : ℂ) (u : Source) : ℝ :=
  ‖plusReadout z u‖^2-‖enlargedReadout z u‖^2

theorem defectPair_split (z w : ℂ) (u v : Source) :
    defectPair z w u v=defectPair z w (tracePart u) (tracePart v)+
      defectPair z w (fiberPart u) (fiberPart v) := by
  unfold defectPair
  rw [plus_trace,plus_trace,plus_fiber_zero,inner_zero_left,
    enlarged_pairing_split z w u v]
  ring

/-- The return consumer charges the entire transported fiber with a minus
sign; it is not an extra positive allowance. -/
theorem fiber_defect_exact (z : ℂ) (hz : 0 ≤ z.im) (u : Source) :
    defectEnergy z (fiberPart u)=-(2*z.im)*‖ambientReadout u‖^2 := by
  have hn : ‖enlargedReadout z (fiberPart u)‖^2=(2*z.im)*‖ambientReadout u‖^2 := by
    rw [enlarged_fiber,WithLp.prod_norm_sq_eq_of_L2]
    change ‖((Real.sqrt (2*z.im) : ℝ) : ℂ) • ambientReadout u‖^2+
      ‖(0 : CanonicalCompletedC3FullWronskianOperatorCarrier)‖^2=_
    rw [norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero,norm_smul,mul_pow]
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt (by positivity : 0 ≤ 2*z.im)]
  unfold defectEnergy
  rw [plus_fiber_zero,hn,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  ring

theorem trace_defect_exact (z : ℂ) (u : Source) :
    defectEnergy z (tracePart u)=‖plusReadout z u‖^2-‖minusReadout z u‖^2 := by
  unfold defectEnergy
  rw [plus_trace,enlarged_trace,WithLp.prod_norm_sq_eq_of_L2]
  simp

theorem enlarged_norm_split (z : ℂ) (u : Source) :
    ‖enlargedReadout z u‖^2=‖enlargedReadout z (tracePart u)‖^2+
      ‖enlargedReadout z (fiberPart u)‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (enlargedReadout z (tracePart u)) (enlargedReadout z (fiberPart u))
    (enlarged_trace_fiber_cross z z u u)
  have he : enlargedReadout z (tracePart u)+enlargedReadout z (fiberPart u)=enlargedReadout z u := by
    rw [← map_add,source_reconstruction]
  rw [he] at h
  simpa only [pow_two] using h

theorem defectEnergy_split (z : ℂ) (u : Source) :
    defectEnergy z u=defectEnergy z (tracePart u)+defectEnergy z (fiberPart u) := by
  unfold defectEnergy
  rw [plus_trace,plus_fiber_zero,enlarged_norm_split]
  simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
  ring

theorem defectEnergy_budget (z : ℂ) (hz : 0 ≤ z.im) (u : Source) :
    defectEnergy z u=‖plusReadout z u‖^2-‖minusReadout z u‖^2-
      (2*z.im)*‖ambientReadout u‖^2 := by
  rw [defectEnergy_split,trace_defect_exact,fiber_defect_exact z hz]
  ring

theorem defect_of_full_zero (z : ℂ) (hz : 0 ≤ z.im) (u : Source)
    (hu : fullReadout z u=0) :
    defectEnergy z u=-(2*z.im)*‖ambientReadout u‖^2 := by
  have hp : plusReadout z u=0 := by
    change canonicalCompletedC3FullWronskianPositiveProjectionMap (fullReadout z u)=0
    rw [hu,map_zero]
  have hm : minusReadout z u=0 := by
    change canonicalCompletedC3FullWronskianNegativeProjectionMap (fullReadout z u)=0
    rw [hu,map_zero]
  rw [defectEnergy_budget z hz,hp,hm,norm_zero]
  ring

end
end CarryFiberTransport
