import NativeMixedCS

/-!
SOURCE-FIRST SIGNED GATE.
Unlike the earlier absolute split, estimates S = alpha B - beta a p AS ONE
correlated scalar from below. Previous shifted-prefix PSD suffices for
R >= u²/h. No premise on the new pivot, S or W sign.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1400000

/-- Core algebraic statement with the signed source term left intact. -/
theorem signed_source_positive_of_head_lower
    (h R S u uHead eu SHead eS : ℝ)
    (hh : 0 < h) (hProjection : u^2 ≤ h*R)
    (hu : |u-uHead| ≤ eu)
    (hS : |S-SHead| ≤ eS)
    (hLower : 0 < |uHead|-eu)
    (hBudget : h*(eS-SHead) < 4*(|uHead|-eu)^2) :
    0 < 4*R+S := by
  have htail : SHead-eS ≤ S := by
    have hlo := (abs_le.mp hS).1
    linarith
  have huupper : |uHead| ≤ |u|+eu := by
    have hab := abs_add_le u (uHead-u)
    have hdiff : |uHead-u| ≤ eu := by
      simpa only [abs_sub_comm] using hu
    have hEq : u+(uHead-u)=uHead := by ring
    rw [hEq] at hab
    linarith
  have hulo : |uHead|-eu ≤ |u| := by linarith
  have hSq : (|uHead|-eu)^2 ≤ u^2 := by
    have hn : 0 ≤ |uHead|-eu := le_of_lt hLower
    have hs : 0 ≤ (|u|- (|uHead|-eu)) * (|u|+ (|uHead|-eu)) :=
      mul_nonneg (sub_nonneg.mpr hulo) (add_nonneg (abs_nonneg _) hn)
    have hsabs : |u|^2=u^2 := sq_abs u
    nlinarith [hs]
  have htailmul := mul_le_mul_of_nonneg_left htail hh.le
  have hmul : 0 < h*(4*R+S) := by
    nlinarith [hProjection, hSq, htailmul, hBudget]
  exact (mul_pos_iff_of_pos_left hh).mp hmul

/-- Native all-order CONDITIONAL implication with the exact old shifted
moment prefix: once the signed TFVD/Green head and tail margin are certified
in that order, the actual Euler-Schur W is strictly positive. -/
theorem native_signed_head_budget_gate
    (s n : ℕ) (r : Fin (n+1) → ℝ)
    (alpha betaA p B R uHead SHead eu eS : ℝ)
    (hPSD : (sourceMomentMatrix nativeH (s+1) (n+1)).PosSemidef)
    (hh : 0 < nativeH (s+1))
    (hR : R = matrixPair (sourceMomentMatrix nativeH (s+1) (n+1)) r r)
    (hu : |nativeMixedU s n r-uHead| ≤ eu)
    (hS : |alpha*B-betaA*p-SHead| ≤ eS)
    (hLower : 0 < |uHead|-eu)
    (hBudget : nativeH (s+1)*(eS-SHead) < 4*(|uHead|-eu)^2) :
    0 < alpha*B-betaA*p+4*R := by
  have hp := nativeMixedU_cs_from_shifted_prefix s n r hPSD hh
  rw [← hR] at hp
  have hconcl := signed_source_positive_of_head_lower
    (nativeH (s+1)) R (alpha*B-betaA*p)
    (nativeMixedU s n r) uHead eu SHead eS
    hh hp hu hS hLower hBudget
  linarith

end
end CarrySourceBezout
