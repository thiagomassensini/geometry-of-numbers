import C3ImpulseExpansion

/-!
True completed source C3/384, joined with exact impulse coefficients and
the 23 proved ORIGINAL tail-jet bounds. No unproved hCoeff premise.
A sharp TT (quadratic) bound remains an explicit independent obligation.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

def originalC3Head384Nat (j : ℕ) : ℂ :=
  literalHead 384 j + originalC3BoundaryJetAny 384 j

def originalC3Tail384Nat (j : ℕ) : ℂ :=
  literalTail 384 j - originalC3BoundaryJetAny 384 j

/-- Exact C3 camera split of the SAME native completed coefficients:
the 12-term boundary is added to the original head and subtracted
from the original tail. -/
theorem original_c3_head_tail384 :
    (fun j => (nativeC j : ℂ)) =
      originalC3Head384Nat + originalC3Tail384Nat := by
  funext j
  have hsrc := congrFun (literal_head_tail 384) j
  simpa [originalC3Head384Nat, originalC3Tail384Nat, Pi.add_apply] using
    hsrc

theorem originalC3Tail384Nat_bound (j : Fin 23) :
    ‖originalC3Tail384Nat j.val‖ ≤ originalC3Box384 j := by
  exact all_twenty_three_c3_bounds j

/-- The exact signed HT+TH correlation has a proved 23-impulse
representation. Every eps_j is a genuine Lean theorem from the completed
C3 source, not a decimal imported as an assumption. -/
theorem original_c3_joint_source_budget384
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (hNB : 2*rB < 23) (hNP : 2*rP < 23)
    (q : ℝ)
    (hQuad : ‖signedSourcePair alpha betaA bB bP rB rP zB zP
       originalC3Tail384Nat originalC3Tail384Nat‖ ≤ q) :
    ‖signedSourcePair alpha betaA bB bP rB rP zB zP
        (fun j => (nativeC j : ℂ)) (fun j => (nativeC j : ℂ)) -
      signedSourcePair alpha betaA bB bP rB rP zB zP
        originalC3Head384Nat originalC3Head384Nat‖ ≤
      (∑ j : Fin 23,
        ‖signedImpulseCoefficient 23 alpha betaA bB bP rB rP zB zP
            originalC3Head384Nat j‖ * originalC3Box384 j) + q := by
  have hEps : ∀ j : Fin 23,
      ‖originalC3Tail384Nat j.val‖ ≤ originalC3Box384 j :=
    originalC3Tail384Nat_bound
  have hCoeff := signed_linear_impulse_expansion
    alpha betaA bB bP rB rP 23 zB zP
    originalC3Head384Nat originalC3Tail384Nat hNB hNP
  have hbudget := signed_source_joint_interval_budget
    alpha betaA bB bP rB rP 23 zB zP
    originalC3Head384Nat originalC3Tail384Nat
    (signedImpulseCoefficient 23 alpha betaA bB bP rB rP zB zP
      originalC3Head384Nat)
    originalC3Box384 q hCoeff hEps hQuad
  rw [original_c3_head_tail384]
  exact hbudget

end
end CarrySourceBezout
