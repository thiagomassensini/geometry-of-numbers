import NativeMixedCS
import SingleModeGate

/-!
Conditional all-order source-first gate. No positivity theorem for the
new pivot is assumed. Input head errors must come from original TFVD
and its completed Green crossings.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000

theorem native_single_mode_head_budget_gate
    (s n : ℕ) (r : Fin (n+1) → ℝ)
    (alpha beta a p B R uHead pHead BHead eu ep eB : ℝ)
    (hPSD : (sourceMomentMatrix nativeH (s+1) (n+1)).PosSemidef)
    (hh : 0 < nativeH (s+1))
    (hR : R = matrixPair (sourceMomentMatrix nativeH (s+1) (n+1)) r r)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hu : |nativeMixedU s n r - uHead| ≤ eu)
    (hp : |p-pHead| ≤ ep)
    (hB : |B-BHead| ≤ eB)
    (hLower : 0 < |uHead|-eu)
    (hBudget :
      nativeH (s+1) *
        (alpha*(|BHead|+eB) + beta*|a| * (|pHead|+ep)) <
      4*(|uHead|-eu)^2) :
    0 < alpha*B - beta*a*p + 4*R := by
  let u := nativeMixedU s n r
  have hcs : u^2 ≤ nativeH (s+1)*R := by
    have hc := nativeMixedU_cs_from_shifted_prefix s n r hPSD hh
    rw [← hR] at hc
    exact hc
  have hUt : |uHead| ≤ |u| + |uHead-u| := by
    calc
      |uHead| = |u + (uHead-u)| := by ring
      _ ≤ |u|+|uHead-u| := abs_add_le _ _
  have hUa : |uHead-u| ≤ eu := by
    simpa only [abs_sub_comm] using hu
  have hUlo : |uHead|-eu ≤ |u| := by linarith
  have hUp : 0 ≤ |uHead|-eu := le_of_lt hLower
  have hSquare : (|uHead|-eu)^2 ≤ u^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hUlo)
      (add_nonneg (abs_nonneg u) hUp)
    have hAbsSq : |u|^2 = u^2 := by
      rcases le_total 0 u with hun | hup
      · rw [abs_of_nonneg hun]
      · rw [abs_of_nonpos hup]; ring
    nlinarith [hprod]
  have hBabs : |B| ≤ |BHead|+eB := by
    calc
      |B| = |BHead+(B-BHead)| := by ring
      _ ≤ |BHead|+|B-BHead| := abs_add_le _ _
      _ ≤ |BHead|+eB := by linarith
  have hPabs : |p| ≤ |pHead|+ep := by
    calc
      |p| = |pHead+(p-pHead)| := by ring
      _ ≤ |pHead|+|p-pHead| := abs_add_le _ _
      _ ≤ |pHead|+ep := by linarith
  have hCost : alpha*|B|+beta*|a*p| ≤
      alpha*(|BHead|+eB)+beta*|a| * (|pHead|+ep) := by
    have h1 := mul_le_mul_of_nonneg_left hBabs hAlpha
    have h2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hPabs (abs_nonneg a)) hBeta
    rw [abs_mul]
    nlinarith
  have hGap : nativeH (s+1)*(alpha*|B|+beta*|a*p|) <
      4*u^2 := by
    have hupper := mul_le_mul_of_nonneg_left hCost hh.le
    nlinarith [hBudget, hSquare]
  exact TiltSchurSingleMode.single_mode_positive
    alpha beta B a p R u (nativeH (s+1)) hAlpha hBeta hh hcs hGap

end
end CarrySourceBezout
