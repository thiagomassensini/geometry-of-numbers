import CanonicalBalance

namespace CarryCriticalEuler
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma NativeMomentOrthogonalization Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Literal original native boundary input in one parity sector. -/
def nativeSectorEnergy (s : Fin 2) (N : ℕ) (v : Fin N → ℝ) : ℝ :=
  nativeSourceFiniteBoundaryEnergy (2*N)
    (if s=0 then nativeSourceBoundaryFromParity N (fun i => (v i:ℂ)) 0
     else nativeSourceBoundaryFromParity N 0 (fun i => (v i:ℂ)))

theorem native_sector_energy_eq (s : Fin 2) (N : ℕ) (v : Fin N → ℝ) :
    nativeSectorEnergy s N v =
      4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s.val N v := by
  rw [nativeSectorEnergy,native_boundary_real_sector,momentForm_eq_sourceMomentQuadratic]

/-- Zero padding is an exact address shift in the same moment form. -/
theorem source_quadratic_shift_two (m : ℕ → ℝ) (s N : ℕ) (v : Fin N → ℝ) :
    sourceMomentQuadratic m s (N+1) (Fin.cons 0 v) = sourceMomentQuadratic m (s+2) N v := by
  simp only [sourceMomentQuadratic,star_trivial,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,zero_mul,mul_zero,zero_add,
    sourceMomentMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : i.succ.val+j.succ.val+s = i.val+j.val+(s+2) := by simp; omega
  rw [he]

/-- For the odd starting sector, the next form is realized by the original
even sector with its zero address retained. No new metric or normalization. -/
def nativeNextEnergy (s : Fin 2) (N : ℕ) (v : Fin N → ℝ) : ℝ :=
  if s=0 then nativeSectorEnergy 1 N v else nativeSectorEnergy 0 (N+1) (Fin.cons 0 v)

theorem native_next_energy_eq (s : Fin 2) (N : ℕ) (v : Fin N → ℝ) :
    nativeNextEnergy s N v =
      4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s.val+1) N v := by
  fin_cases s
  · simp [nativeNextEnergy,native_sector_energy_eq]
  · simp only [nativeNextEnergy,native_sector_energy_eq]
    rw [source_quadratic_shift_two]
    rfl

theorem native_critical_energy_eq (s : Fin 2) (d : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val d)) :
    nativeSectorEnergy s (d+1) (canonicalCriticalVector s.val d) =
      4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s.val d :=
  native_inverseSchur_boundary_energy s d hA

/-- Exact balance in the original Green boundary energies, including all
mixed terms through the Schur cancellation and the retained lower residual. -/
theorem native_weighted_balance (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val (n+1))) :
    4*weightedForm canonicalCompletedNativeLogDerivativeMoment s.val (canonicalCriticalVector s.val (n+1)) =
      ((2*((n+1:ℕ):ℝ)+(s.val:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s.val:ℝ)+3))*
        nativeNextEnergy s (n+2) (canonicalCriticalVector s.val (n+1)) -
      (16*((n+1:ℕ):ℝ)+8*(s.val:ℝ)+6)*canonicalCriticalVector s.val (n+1) (Fin.last n).castSucc*
        nativeSectorEnergy s (n+2) (canonicalCriticalVector s.val (n+1)) +
      4*nativeNextEnergy s (n+1) (eulerResidual n (canonicalCriticalVector s.val (n+1))) := by
  rw [native_next_energy_eq,native_critical_energy_eq s (n+1) hA,native_next_energy_eq,
    canonical_weighted_reduction s.val n hA]
  ring

end
end CarryCriticalEuler
