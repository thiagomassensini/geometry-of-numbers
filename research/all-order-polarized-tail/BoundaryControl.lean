import CriticalScale

namespace CarrySourceTail
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryThetaPattern
open scoped BigOperators ComplexConjugate Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Literal inherited factor 4 and original parity chart, with both real
quadratures. It identifies no material-depth index with a source jet index. -/
theorem sourcePair_boundary (n : ℕ) (e o : Fin n → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) (nativeSourceBoundaryFromParity n e o) =
      4*((sourcePair 0 e e).re+(sourcePair 1 o o).re) := by
  rw [nativeSourceFiniteBoundaryEnergy_even_split,
    nativeSourceEvenBoundaryPhase_fromParity,nativeSourceOddBoundaryPhase_fromParity,
    primeDepthGeometricMoment_eq_canonical]
  simp only [sourcePair,Complex.re_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,sub_zero,
    mul_sub,mul_assoc]

/-- All remaining orders M are allowed. This bound transports the signed
source form, not a positive substitute, into its actual boundary readout. -/
theorem boundary_all_order_lower_bound {M : ℕ}
    (e o : Fin 5 → ℂ) (a b : Fin M → ℂ) :
    -4*cutoffError 0 5*(coefficientEnergy e+coefficientEnergy a)-
      4*cutoffError 1 5*(coefficientEnergy o+coefficientEnergy b) ≤
      nativeSourceFiniteBoundaryEnergy (2*(5+M))
        (nativeSourceBoundaryFromParity (5+M) (Fin.append e a) (Fin.append o b)) := by
  rw [sourcePair_boundary]
  have he := all_order_lower_bound_from_certified_five 0 e a
  have ho := all_order_lower_bound_from_certified_five 1 o b
  norm_num only [Fin.val_zero,Fin.val_one] at he ho
  linarith

/-- Central normalization regression: no factor is fitted downstream. -/
theorem sourcePair_central (s : ℕ) :
    sourcePair s (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => (1:ℂ)) = (h s:ℂ) := by
  simp [sourcePair]

/-- First crossing with independently chosen arguments and both phases. -/
theorem first_crossing_regression (s : ℕ) (x y a b : ℂ) :
    sourcePair s (Fin.append (fun _ : Fin 1 => x) (fun _ : Fin 1 => a))
      (Fin.append (fun _ : Fin 1 => y) (fun _ : Fin 1 => b)) =
      (h s:ℂ)*conj x*y+(h (s+1):ℂ)*conj x*b+
        (h (s+1):ℂ)*conj a*y+(h (s+2):ℂ)*conj a*b := by
  rw [sourcePair_append]
  simp [sourcePair]

end
end CarrySourceTail
