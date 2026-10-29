import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import Mathlib.Tactic

/-! Exact fibers of the EXISTING physical one-point trace projection.
No source, metric or normalization is changed. The factor 1/2 is forced by
adding two trace legs; it is not a canonical-moment calibration. -/
namespace CarryTraceFiber
open CarrySelfAdjointOperator
open CanonicalCompletedC3AllCutoffOnePointHilbert
open scoped InnerProductSpace ComplexConjugate
noncomputable section

abbrev Physical := CanonicalCompletedC3AllCutoffOnePointHilbert
abbrev Trace := CompletedScalarBoundaryTraceCarrier
abbrev projection := canonicalCompletedC3OnePointCompletedTraceProjection

def headTrace (x : Physical) : Trace := WithLp.toLp 2 (Complex.I*x.logJetHead, x.valueHead)
def tailTrace (x : Physical) : Trace := WithLp.toLp 2 (Complex.I*x.logJetTail, x.valueTail)
def contrast (x : Physical) : Trace := headTrace x-tailTrace x

theorem projection_eq_add (x : Physical) : projection x = headTrace x+tailTrace x := by
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply]
  apply WithLp.ofLp_injective 2
  ext <;> simp [headTrace, tailTrace, completedCompanion, completedValue, mul_add]

theorem head_reconstruction (x : Physical) : headTrace x = (2 : ℝ)⁻¹ • (projection x+contrast x) := by
  rw [projection_eq_add, contrast]
  module

theorem tail_reconstruction (x : Physical) : tailTrace x = (2 : ℝ)⁻¹ • (projection x-contrast x) := by
  rw [projection_eq_add, contrast]
  module

/-- The original three vector channels, with two independent arguments. -/
def bulkPairing (x y : Physical) : ℝ :=
  inner ℝ x.direct y.direct + inner ℝ x.reflected y.reflected +
    inner ℝ x.quarterTurnReflected y.quarterTurnReflected

private theorem rotated_inner (a b : ℂ) : inner ℝ (Complex.I*a) (Complex.I*b) = inner ℝ a b := by
  change (inner ℂ (Complex.I*a) (Complex.I*b)).re = (inner ℂ a b).re
  simp [RCLike.inner_apply, map_mul, Complex.conj_I]

/-- Native physical pairing BEFORE a boundary projection. -/
theorem physical_inner_head_tail (x y : Physical) :
    inner ℝ x y = bulkPairing x y+inner ℝ (headTrace x) (headTrace y)+
      inner ℝ (tailTrace x) (tailTrace y) := by
  simp only [bulkPairing, headTrace, tailTrace, WithLp.prod_inner_apply,
    rotated_inner]
  simp only [direct, reflected, quarterTurnReflected, valueHead, logJetHead, valueTail, logJetTail]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

/-- Every ordered cross is retained. -/
theorem physical_inner_fiber (x y : Physical) :
    inner ℝ x y = bulkPairing x y +
      (1/2 : ℝ)*inner ℝ (projection x) (projection y) +
      (1/2 : ℝ)*inner ℝ (contrast x) (contrast y) := by
  rw [physical_inner_head_tail, projection_eq_add, projection_eq_add, contrast, contrast]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

theorem physical_norm_fiber (x : Physical) :
    ‖x‖^2 = ‖x.direct‖^2+‖x.reflected‖^2+‖x.quarterTurnReflected‖^2 +
      (1/2 : ℝ)*‖projection x‖^2+(1/2 : ℝ)*‖contrast x‖^2 := by
  simpa only [bulkPairing, real_inner_self_eq_norm_sq] using physical_inner_fiber x x

/-- All retained data reconstruct the physical state; no quotient is taken. -/
theorem physical_eq_iff (x y : Physical) : x=y ↔
    x.direct=y.direct ∧ x.reflected=y.reflected ∧
    x.quarterTurnReflected=y.quarterTurnReflected ∧
    projection x=projection y ∧ contrast x=contrast y := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · rintro ⟨hd,hr,hq,hp,hc⟩
    have hh : headTrace x=headTrace y := by rw [head_reconstruction x,head_reconstruction y,hp,hc]
    have ht : tailTrace x=tailTrace y := by rw [tail_reconstruction x,tail_reconstruction y,hp,hc]
    have hhv := congrArg (fun t : Trace => t.snd) hh
    have hhl := congrArg (fun t : Trace => t.fst) hh
    have htv := congrArg (fun t : Trace => t.snd) ht
    have htl := congrArg (fun t : Trace => t.fst) ht
    change x.valueHead=y.valueHead at hhv
    change Complex.I*x.logJetHead=Complex.I*y.logJetHead at hhl
    change x.valueTail=y.valueTail at htv
    change Complex.I*x.logJetTail=Complex.I*y.logJetTail at htl
    have hhl1 := mul_left_cancel₀ Complex.I_ne_zero hhl
    have htl1 := mul_left_cancel₀ Complex.I_ne_zero htl
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hd
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · exact hr
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · exact hq
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · exact hhv
          · apply WithLp.ofLp_injective 2
            apply Prod.ext
            · exact hhl1
            · apply WithLp.ofLp_injective 2
              exact Prod.ext htv htl1

theorem projection_zero_iff (x : Physical) : projection x=0 ↔ headTrace x = -tailTrace x := by
  rw [projection_eq_add, add_eq_zero_iff_eq_neg]

theorem projection_defect_exact (x : Physical) :
    ‖x‖^2-(1/2 : ℝ)*‖projection x‖^2 =
      ‖x.direct‖^2+‖x.reflected‖^2+‖x.quarterTurnReflected‖^2 +
        (1/2 : ℝ)*‖contrast x‖^2 := by rw [physical_norm_fiber]; ring

theorem projection_defect_nonnegative (x : Physical) :
    0 ≤ ‖x‖^2-(1/2 : ℝ)*‖projection x‖^2 := by
  rw [projection_defect_exact]
  positivity


/-- The fixed minimum-energy section of the EXISTING trace map.
The two legs receive equal halves. No source value or moment selects it. -/
def balancedLift (t : Trace) : Physical :=
  WithLp.toLp 2 (0, WithLp.toLp 2 (0, WithLp.toLp 2 (0,
    WithLp.toLp 2 (t.snd/2, WithLp.toLp 2 ((-Complex.I*t.fst)/2,
      WithLp.toLp 2 (t.snd/2, (-Complex.I*t.fst)/2))))))

theorem projection_balancedLift (t : Trace) : projection (balancedLift t)=t := by
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  all_goals dsimp [balancedLift, completedCompanion, completedValue, logJetHead,
    logJetTail, valueHead, valueTail]
  · ring_nf
    simp
  · ring

theorem contrast_balancedLift (t : Trace) : contrast (balancedLift t)=0 := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [contrast, headTrace, tailTrace, balancedLift,
    logJetHead, logJetTail, valueHead, valueTail]

theorem bulkPairing_balancedLift (t : Trace) (y : Physical) :
    bulkPairing (balancedLift t) y=0 := by
  simp [bulkPairing, balancedLift, direct, reflected, quarterTurnReflected]

theorem balancedLift_inner (t u : Trace) :
    inner ℝ (balancedLift t) (balancedLift u)=(1/2 : ℝ)*inner ℝ t u := by
  rw [physical_inner_fiber, bulkPairing_balancedLift, projection_balancedLift,
    projection_balancedLift, contrast_balancedLift, inner_zero_left]
  ring

/-- A bookkeeping component inside the SAME physical Hilbert, not a discarded state. -/
def invisible (x : Physical) : Physical := x-balancedLift (projection x)

theorem projection_invisible (x : Physical) : projection (invisible x)=0 := by
  rw [invisible, map_sub, projection_balancedLift, sub_self]

theorem invisible_orthogonal (t : Trace) (x : Physical) :
    inner ℝ (balancedLift t) (invisible x)=0 := by
  rw [invisible, inner_sub_right, balancedLift_inner]
  rw [physical_inner_fiber (balancedLift t) x, bulkPairing_balancedLift,
    projection_balancedLift, contrast_balancedLift, inner_zero_left]
  ring

theorem physical_reconstruct (x : Physical) : balancedLift (projection x)+invisible x=x := by
  rw [invisible]
  abel

/-- Lossless polarization in the original metric. -/
theorem physical_inner_visible_invisible (x y : Physical) :
    inner ℝ x y=(1/2 : ℝ)*inner ℝ (projection x) (projection y)+
      inner ℝ (invisible x) (invisible y) := by
  have hxy : inner ℝ x y = inner ℝ
      (balancedLift (projection x)+invisible x)
      (balancedLift (projection y)+invisible y) := by
    rw [physical_reconstruct,physical_reconstruct]
  have hrev : inner ℝ (invisible x) (balancedLift (projection y))=0 := by
    rw [real_inner_comm]
    exact invisible_orthogonal _ _
  rw [hxy, inner_add_left, inner_add_right, inner_add_right,
    invisible_orthogonal, hrev, balancedLift_inner]
  ring

theorem invisible_norm_exact (x : Physical) :
    ‖invisible x‖^2 = ‖x.direct‖^2+‖x.reflected‖^2+‖x.quarterTurnReflected‖^2 +
      (1/2 : ℝ)*‖contrast x‖^2 := by
  have h := physical_inner_visible_invisible x x
  simp only [real_inner_self_eq_norm_sq] at h
  rw [physical_norm_fiber] at h
  linarith

/-- The minimum norm in a trace fiber is attained without changing the metric. -/
theorem balancedLift_minimum (x : Physical) : ‖balancedLift (projection x)‖^2 ≤ ‖x‖^2 := by
  have h := balancedLift_inner (projection x) (projection x)
  simp only [real_inner_self_eq_norm_sq] at h
  rw [h]
  linarith [projection_defect_nonnegative x]


theorem physical_norm_visible_invisible (x : Physical) :
    ‖x‖^2=(1/2 : ℝ)*‖projection x‖^2+‖invisible x‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using physical_inner_visible_invisible x x

theorem trace_energy_preserved_iff (x : Physical) :
    ‖x‖^2=(1/2 : ℝ)*‖projection x‖^2 ↔ invisible x=0 := by
  rw [physical_norm_visible_invisible]
  constructor
  · intro h
    have hn : ‖invisible x‖^2=0 := by linarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (invisible x)])
  · intro h
    simp [h]

/-- Complete finite synthesis precedes both projections, for independent
coefficient families and independent physical source families. -/
theorem finite_synthesis_pairing {N M : ℕ} (c : Fin N → ℝ) (d : Fin M → ℝ)
    (x : Fin N → Physical) (y : Fin M → Physical) :
    inner ℝ (∑ i, c i • x i) (∑ j, d j • y j)=
      (1/2 : ℝ)*inner ℝ (projection (∑ i, c i • x i)) (projection (∑ j, d j • y j))+
        inner ℝ (invisible (∑ i, c i • x i)) (invisible (∑ j, d j • y j)) :=
  physical_inner_visible_invisible _ _

theorem finite_synthesis_energy_defect {N : ℕ} (c : Fin N → ℝ) (x : Fin N → Physical) :
    ‖∑ i, c i • x i‖^2-(1/2 : ℝ)*‖projection (∑ i, c i • x i)‖^2=
      ‖invisible (∑ i, c i • x i)‖^2 := by
  rw [physical_norm_visible_invisible]
  ring

end
end CarryTraceFiber
