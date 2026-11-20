import NativeSignedGate
import ProjectedCauchy

/-!
Sharp OLD PREFIX variant for the actual Euler residual, whose last Schur
coefficient is zero. The earlier Fin (n+1) generic gate unnecessarily asks
for an (n+1)-dimensional shifted PSD block. This theorem needs only Fin n.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
noncomputable section
set_option maxHeartbeats 1000000

/-- A genuinely prior-prefix sufficient condition; the new pivot has
no sign assumption, and no enlargement of the PSD prefix occurs. -/
theorem native_signed_gate_of_old_prefix
    (s n : ℕ) (r e : Fin n → ℝ)
    (R S uHead SHead eu eS : ℝ)
    (hPSD : (sourceMomentMatrix nativeH (s+1) n).PosSemidef)
    (hh : 0 < nativeH (s+1))
    (hWeight : TiltSchurProjectedCS.pair
        (sourceMomentMatrix nativeH (s+1) n) e e = nativeH (s+1))
    (hR : R = TiltSchurProjectedCS.pair
        (sourceMomentMatrix nativeH (s+1) n) r r)
    (hu : |TiltSchurProjectedCS.pair
        (sourceMomentMatrix nativeH (s+1) n) r e-uHead| ≤ eu)
    (hS : |S-SHead| ≤ eS)
    (hLower : 0 < |uHead|-eu)
    (hBudget : nativeH (s+1)*(eS-SHead) < 4*(|uHead|-eu)^2) :
    0 < 4*R+S := by
  let H := sourceMomentMatrix nativeH (s+1) n
  have hsym : H.transpose = H := sourceMomentMatrix_transpose (s+1) n
  have hcs := TiltSchurProjectedCS.projected_cs H hPSD hsym r e (by
    rw [hWeight]
    exact hh)
  have hProjected :
      (TiltSchurProjectedCS.pair H r e)^2 ≤ nativeH (s+1)*R := by
    rw [hWeight, ← hR] at hcs
    exact hcs
  exact signed_source_positive_of_head_lower
    (nativeH (s+1)) R S
    (TiltSchurProjectedCS.pair H r e) uHead eu SHead eS
    hh hProjected hu hS hLower hBudget

/-- Explicit first coordinate of the same shifted prefix (not a new
TFVD seed). This remains meaningful only when the old prefix is nonempty. -/
def firstCore (n : ℕ) (hn : 0 < n) : Fin n → ℝ :=
  fun i => if i = ⟨0,hn⟩ then 1 else 0

theorem firstCore_weight (s n : ℕ) (hn : 0 < n) :
    TiltSchurProjectedCS.pair
        (sourceMomentMatrix nativeH (s+1) n)
        (firstCore n hn) (firstCore n hn) = nativeH (s+1) := by
  simp [TiltSchurProjectedCS.pair, firstCore, sourceMomentMatrix,
    Matrix.mulVec, dotProduct, Nat.add_assoc]

end
end CarrySourceBezout
