import LeadingObstruction

namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open CarryCriticalRelative CarryForcingResidual NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

def pr41Incident (s : Fin 2) (n k : ℕ) : PhysicalCauchySpace :=
  physicalIncident (n+1) k (nativeResidualBoundary s n)
def pr41Returned (s : Fin 2) (n k : ℕ) : PhysicalCauchySpace :=
  physicalReturned (n+1) k (nativeResidualBoundary s n)

def pr41TransportCorrection (R : ℕ) (s : Fin 2) (n k : ℕ) : ℝ :=
  -2*(inner ℂ (conservativeReturn R (pr41Incident s n k))
    (transportDefect R (pr41Incident s n k) (pr41Returned s n k))).re-
    ‖transportDefect R (pr41Incident s n k) (pr41Returned s n k)‖^2

/-- Full defect extraction on the exact PR41 monic source, before any sign. -/
theorem pr41_conservative_ledger (R : ℕ) (s : Fin 2) (n k : ℕ) :
    ‖pr41Incident s n k‖^2-‖pr41Returned s n k‖^2=
      ‖conservativeHead R (pr41Incident s n k)‖^2+pr41TransportCorrection R s n k := by
  rw [energy_defect_ledger]
  unfold pr41TransportCorrection
  ring

theorem pr41_conservative_ledger_tendsto (R : ℕ) (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => ‖conservativeHead R (pr41Incident s n k)‖^2+
      pr41TransportCorrection R s n k) atTop
      (nhds (2*carryPairingPivot (hankelPairing (fun j => h (j+s.val))) n)) := by
  have ht := (physical_signed_energy_tendsto (n+1) (nativeResidualBoundary s n)).div_const 2
  rw [nativeResidualBoundary_energy] at ht
  have he : 4*carryPairingPivot (hankelPairing (fun j => h (j+s.val))) n/2=
      2*carryPairingPivot (hankelPairing (fun j => h (j+s.val))) n := by ring
  rw [he] at ht
  convert ht using 1
  funext k
  rw [← pr41_conservative_ledger]
  simp only [pr41Incident,pr41Returned,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)]

def pr41Order (s : Fin 2) (n : ℕ) : ℕ := 2*n+s.val

theorem pr41Order_lt (s : Fin 2) (n : ℕ) : pr41Order s n<2*(n+1) := by
  have hs := s.isLt
  unfold pr41Order
  omega

theorem pr41Boundary_above (s : Fin 2) (n : ℕ) (a : Fin (2*(n+1)))
    (ha : pr41Order s n<a.val) : nativeResidualBoundary s n a=0 := by
  fin_cases s
  · have ham : a.val%2≠0 := by
      have hlt := a.isLt
      simp only [pr41Order] at ha
      omega
    simp [nativeResidualBoundary,nativeSourceBoundaryFromParity,ham]
  · have hlt := a.isLt
    simp only [pr41Order] at ha
    omega

theorem pr41_monic_top (s : Fin 2) (n : ℕ) :
    CarryForcingResidual.criticalCoefficients s n (Fin.last n)=1 := by
  have hm := residualPolynomial_monic_degree (fun k => h (k+s.val)) n n le_rfl
  have hd := Polynomial.natDegree_eq_of_degree_eq_some hm.2
  change (residualPolynomial (fun k => h (k+s.val)) n n).coeff n=1
  have hh : (residualPolynomial (fun k => h (k+s.val)) n n).coeff
      (residualPolynomial (fun k => h (k+s.val)) n n).natDegree=1 := by
    rw [Polynomial.coeff_natDegree]
    exact hm.1
  simpa only [hd] using hh

theorem pr41Boundary_top (s : Fin 2) (n : ℕ) :
    nativeResidualBoundary s n ⟨pr41Order s n,pr41Order_lt s n⟩=
      (((-1:ℝ)^n:ℝ):ℂ) := by
  fin_cases s
  · have hd : (2*n+0)/2=n := by omega
    have hm : (2*n+0)%2=0 := by omega
    change (((-1:ℝ)^((2*n+0)/2):ℝ):ℂ)*
      (if (2*n+0)%2=0 then ((orthogonalPolynomial (fun k => h (k+0)) n).coeff ((2*n+0)/2):ℂ) else 0)=_
    rw [hd,if_pos hm]
    change (((-1:ℝ)^n:ℝ):ℂ)*(CarryForcingResidual.criticalCoefficients 0 n (Fin.last n):ℂ)=_
    rw [pr41_monic_top 0 n,Complex.ofReal_one,mul_one]
  · have hd : (2*n+1)/2=n := by omega
    have hm : (2*n+1)%2≠0 := by omega
    change (((-1:ℝ)^((2*n+1)/2):ℝ):ℂ)*
      (if (2*n+1)%2=0 then 0 else ((orthogonalPolynomial (fun k => h (k+1)) n).coeff ((2*n+1)/2):ℂ))=_
    rw [hd,if_neg hm]
    change (((-1:ℝ)^n:ℝ):ℂ)*(CarryForcingResidual.criticalCoefficients 1 n (Fin.last n):ℂ)=_
    rw [pr41_monic_top 1 n,Complex.ofReal_one,mul_one]

theorem pr41Boundary_top_ne (s : Fin 2) (n : ℕ) :
    nativeResidualBoundary s n ⟨pr41Order s n,pr41Order_lt s n⟩≠0 := by
  rw [pr41Boundary_top]
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero n (by norm_num))

/-- Every exact PR41 direction has a nonvanishing leading transport defect
for every fixed positive shift power, without invertibility or sign inputs. -/
theorem pr41_conservative_return_fails (R : ℕ) (s : Fin 2) (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, pr41Returned s n k≠conservativeReturn R (pr41Incident s n k) :=
  conservative_return_not_eventually_source R (n+1) (pr41Order s n) (nativeResidualBoundary s n)
    (pr41Order_lt s n) (pr41Boundary_above s n) (pr41Boundary_top_ne s n)

end
end CarryConservativeIntertwiner
