import NativeMixedU
import ProjectedCauchy

/-!
Exact Cauchy-Schwarz inside the prior shifted ORIGINAL native moment prefix.
Does not claim this prefix is unconditionally PSD at all orders.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1000000

theorem firstPolynomial_norm (s n : ℕ) :
    TiltSchurProjectedCS.pair
      (sourceMomentMatrix nativeH (s+1) (n+1))
      (firstPolynomial n) (firstPolynomial n) = nativeH (s+1) := by
  simp [TiltSchurProjectedCS.pair, firstPolynomial, Matrix.mulVec,
    dotProduct, sourceMomentMatrix, Nat.add_assoc]

theorem sourceMomentMatrix_transpose (s n : ℕ) :
    (sourceMomentMatrix nativeH s n).transpose =
      sourceMomentMatrix nativeH s n := by
  ext i j
  simp [sourceMomentMatrix, Matrix.transpose_apply, Nat.add_comm]

/-- For the actual signed native scalar u, PSD of the *prior shifted*
prefix supplies exactly the projection inequality required by the
single-mode positivity gate. Nothing about the new pivot is assumed. -/
theorem nativeMixedU_cs_from_shifted_prefix (s n : ℕ)
    (r : Fin (n+1) → ℝ)
    (hPSD : (sourceMomentMatrix nativeH (s+1) (n+1)).PosSemidef)
    (hfirst : 0 < nativeH (s+1)) :
    (nativeMixedU s n r)^2 ≤
      nativeH (s+1) *
        matrixPair (sourceMomentMatrix nativeH (s+1) (n+1)) r r := by
  let H := sourceMomentMatrix nativeH (s+1) (n+1)
  let e := firstPolynomial n
  have he : TiltSchurProjectedCS.pair H e e = nativeH (s+1) :=
    firstPolynomial_norm s n
  have hpos : 0 < TiltSchurProjectedCS.pair H e e := by
    rw [he]
    exact hfirst
  have hsym : H.transpose = H := sourceMomentMatrix_transpose (s+1) (n+1)
  have hcs := TiltSchurProjectedCS.projected_cs H hPSD hsym r e hpos
  calc
    (nativeMixedU s n r)^2 = (TiltSchurProjectedCS.pair H r e)^2 := by
      rw [nativeMixedU_pair]
      rfl
    _ ≤ (TiltSchurProjectedCS.pair H e e) *
          TiltSchurProjectedCS.pair H r r := hcs
    _ = nativeH (s+1) * matrixPair H r r := by rw [he]; rfl

end
end CarrySourceBezout
