import BoundaryFeedback
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! A finite independent control, not a replacement Carry source. The two
incident vectors are independent; return acts by 1/2 and 2 on them. A positive
anchor deficit alone therefore cannot force positivity on the remainder. -/
namespace CarryReturnDeflation
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev ControlSpace := WithLp 2 (ℂ × ℂ)
def controlAnchor : ControlSpace := WithLp.toLp 2 ((1:ℂ),0)
def controlIncident : ControlSpace := WithLp.toLp 2 ((0:ℂ),1)
def controlReturned : ControlSpace := (2:ℂ) • controlIncident

theorem control_anchor_deficit_pos : 0 < (deficit (1/2:ℂ)).re := by
  norm_num [deficit, map_ofNat]

theorem control_feedback_incident_zero :
    feedbackIn (1/2:ℂ) controlIncident controlReturned = 0 := by
  simp only [feedbackIn,controlReturned,smul_smul]
  norm_num [map_ofNat]

theorem control_original_negative :
    balance controlIncident controlReturned controlIncident controlReturned = -3 := by
  simp only [balance,controlReturned,inner_smul_left,inner_smul_right,
    controlIncident,WithLp.prod_inner_apply]
  norm_num [map_ofNat]

theorem control_remainder_negative :
    inner ℂ (feedbackIn (1/2:ℂ) controlIncident controlReturned)
      (feedbackIn (1/2:ℂ) controlIncident controlReturned) -
      inner ℂ (feedbackOut (1/2:ℂ) controlIncident controlReturned)
        (feedbackOut (1/2:ℂ) controlIncident controlReturned) = -(9/4:ℂ) := by
  rw [← feedback_balance,control_original_negative]
  norm_num [deficit, map_ofNat]

theorem control_anchor_incident_independent :
    ∀ a b : ℂ, a • controlAnchor + b • controlIncident = 0 → a=0 ∧ b=0 := by
  intro a b hh
  have hfirst := congrArg (fun x : ControlSpace => x.fst) hh
  have hsecond := congrArg (fun x : ControlSpace => x.snd) hh
  simpa [controlAnchor,controlIncident] using And.intro hfirst hsecond

end
end CarryReturnDeflation
