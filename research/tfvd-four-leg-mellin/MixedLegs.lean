import GradientMellin

namespace CarryFourLeg
open CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
noncomputable section
set_option autoImplicit false

private theorem legs_ext {ι : Type*} {a b : ReflectedBoundarySynthesisData ι}
    (hl : a.left = b.left) (hr : a.right = b.right)
    (hjl : a.jetLeft = b.jetLeft) (hjr : a.jetRight = b.jetRight) : a = b := by
  cases a
  cases b
  cases hl
  cases hr
  cases hjl
  cases hjr
  rfl

theorem mixed_value_decode {kappa : ℂ} (hk : kappa ≠ 0)
    (omega : ℕ → ℂ) (ho : ∀ m, omega m ≠ 0) (m : ℕ) (z w : ℂ) :
    enrichedAngularTfvdDecode kappa (omega m)
      ((canonicalMixedBoundaryResidualPair kappa omega z w).value.blocks m) =
      ({first := positiveDirichletGradient w (3*m),
        second := positiveDirichletGradient w (3*m+1),
        dormant := positiveDirichletGradient w (3*m+2)} : TfvdThreeEdges) := by
  exact enrichedAngularTfvdDecode_encode m hk (ho m) _ _ _

theorem mixed_log_decode {kappa : ℂ} (hk : kappa ≠ 0)
    (omega : ℕ → ℂ) (ho : ∀ m, omega m ≠ 0) (m : ℕ) (z w : ℂ) :
    enrichedAngularTfvdDecode kappa (omega m)
      ((canonicalMixedBoundaryResidualPair kappa omega z w).logJet.blocks m) =
      ({first := positiveLogDirichletGradient z (3*m),
        second := positiveLogDirichletGradient z (3*m+1),
        dormant := positiveLogDirichletGradient z (3*m+2)} : TfvdThreeEdges) := by
  exact enrichedAngularTfvdDecode_encode m hk (ho m) _ _ _

/-- The two retained edge roles share the middle gradient before any sum.
These addresses are consequences of decoding the original source. -/
def addressedGradientLegs (M : ℕ) (z w : ℂ) :
    ReflectedBoundarySynthesisData (Fin M × Fin 2) where
  left mr := positiveDirichletGradient w (3*mr.1.val+mr.2.val)
  right mr := positiveDirichletGradient w (3*mr.1.val+mr.2.val+1)
  jetLeft mr := positiveLogDirichletGradient z (3*mr.1.val+mr.2.val)
  jetRight mr := positiveLogDirichletGradient z (3*mr.1.val+mr.2.val+1)

theorem original_mixed_legs_addresses (M : ℕ) {kappa : ℂ} (hk : kappa ≠ 0)
    (omega : ℕ → ℂ) (ho : ∀ m, omega m ≠ 0) (z w : ℂ) :
    canonicalMixedBoundaryResidualLegs M kappa omega z w = addressedGradientLegs M z w := by
  apply legs_ext
  · funext mr
    rcases mr with ⟨m,r⟩
    fin_cases r <;>
      simp [canonicalMixedBoundaryResidualLegs, enrichedTfvdBoundaryEdgeLeft,
        mixed_value_decode hk omega ho, addressedGradientLegs]
    rfl
  · funext mr
    rcases mr with ⟨m,r⟩
    fin_cases r <;>
      simp [canonicalMixedBoundaryResidualLegs, enrichedTfvdBoundaryEdgeRight,
        mixed_value_decode hk omega ho, addressedGradientLegs, Nat.add_assoc]
    rfl
  · funext mr
    rcases mr with ⟨m,r⟩
    fin_cases r <;>
      simp [canonicalMixedBoundaryResidualLegs, enrichedTfvdBoundaryEdgeJetLeft,
        mixed_log_decode hk omega ho, addressedGradientLegs]
    rfl
  · funext mr
    rcases mr with ⟨m,r⟩
    fin_cases r <;>
      simp [canonicalMixedBoundaryResidualLegs, enrichedTfvdBoundaryEdgeJetRight,
        mixed_log_decode hk omega ho, addressedGradientLegs, Nat.add_assoc]
    rfl

/-- Images of all four ORIGINAL leg roles. Each entry is an integral pair
of one literal heat edge before the required coordinate is selected.
The two material parameters remain independent. -/
def heatMixedLegs (M : ℕ) (z w : ℂ) :
    ReflectedBoundarySynthesisData (Fin M × Fin 2) where
  left mr := (materialEdgeTrace (3*mr.1.val+mr.2.val) w).1
  right mr := (materialEdgeTrace (3*mr.1.val+mr.2.val+1) w).1
  jetLeft mr := (materialEdgeTrace (3*mr.1.val+mr.2.val) z).2
  jetRight mr := (materialEdgeTrace (3*mr.1.val+mr.2.val+1) z).2

theorem heat_mixed_legs_calibration (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    heatMixedLegs M z w = addressedGradientLegs M z w := by
  apply legs_ext
  · funext mr
    exact congrArg Prod.fst (material_edge_trace_eq _ hw)
  · funext mr
    exact congrArg Prod.fst (material_edge_trace_eq _ hw)
  · funext mr
    exact congrArg Prod.snd (material_edge_trace_eq _ hz)
  · funext mr
    exact congrArg Prod.snd (material_edge_trace_eq _ hz)

/-- Whole four-leg equality is proved before the boundary pairing.
All finite cutoffs are allowed; M=1 is the first regression. -/
theorem original_four_legs_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    heatMixedLegs M z w =
      canonicalMixedBoundaryResidualLegs M tfvdHaarScale (fun _ => 1) z w := by
  rw [heat_mixed_legs_calibration M hz hw,
    original_mixed_legs_addresses M tfvdHaarScale_ne_zero (fun _ => 1) (by simp)]

theorem middle_value_edge_shared (M : ℕ) (m : Fin M) (z w : ℂ) :
    (heatMixedLegs M z w).right (m,0) = (heatMixedLegs M z w).left (m,1) := rfl

theorem middle_log_edge_shared (M : ℕ) (m : Fin M) (z w : ℂ) :
    (heatMixedLegs M z w).jetRight (m,0) = (heatMixedLegs M z w).jetLeft (m,1) := rfl

end
end CarryFourLeg
