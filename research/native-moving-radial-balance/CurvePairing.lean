import OriginalCurve

namespace CarryMovingRadial
open CarrySelfAdjointOperator NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def fullPair (N : ℕ) (q c d : Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, ∑ j : Fin N,
    conj (c i)*d j*(1-conj (q i)*q j)/((i:ℂ)+(j:ℂ)+2)

theorem fixedSynthesis_pairing (N : ℕ) (c d : Fin N → ℂ) :
    inner ℂ (fixedSynthesis N c) (fixedSynthesis N d)=
      ∑ i : Fin N, ∑ j : Fin N, conj (c i)*d j/((i:ℂ)+(j:ℂ)+2) := by
  unfold fixedSynthesis
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Full complex polarization AFTER equality of BOTH complete physical legs. -/
theorem curve_full_pair (N : ℕ) (h : ℝ) (x y : Fin N → ℂ) :
    2*canonicalCompletedNativeProjectiveChiralForm (curveState N h x) (curveState N h y)=
      fullPair N (fun r => curveQuotient h r)
        (curveCoefficients N h x) (curveCoefficients N h y) := by
  rw [curve_legs,curve_legs]
  unfold canonicalCompletedNativeProjectiveChiralForm
  norm_num only [Prod.fst,Prod.snd]
  rw [fixedSynthesis_pairing,fixedSynthesis_pairing]
  unfold fullPair
  simp_rw [← Finset.sum_sub_distrib]
  have he : ∀ i j : Fin N,
      conj (curveCoefficients N h x i)*curveCoefficients N h y j/((i:ℂ)+(j:ℂ)+2)-
      conj (curveCoefficients N h x i*curveQuotient h i)*
        (curveCoefficients N h y j*curveQuotient h j)/((i:ℂ)+(j:ℂ)+2)=
      conj (curveCoefficients N h x i)*curveCoefficients N h y j*
        (1-conj (curveQuotient h i)*curveQuotient h j)/((i:ℂ)+(j:ℂ)+2) := by
    intro i j
    simp only [map_mul]
    ring
  simp_rw [he]
  ring

theorem curve_norm_balance (N : ℕ) (h : ℝ) (x : Fin N → ℂ) :
    ‖(curveState N h x).1‖^2-‖(curveState N h x).2‖^2=
      (fullPair N (fun r => curveQuotient h r)
        (curveCoefficients N h x) (curveCoefficients N h x)).re := by
  have he := congrArg Complex.re (curve_full_pair N h x x)
  have hn := CarryTailReturn.signed_diagonal_norm (curveState N h x)
  norm_num [Complex.mul_re] at he
  exact hn.symm.trans he

/-- The precise native-grid identification missing from the previous report.
The ORIGINAL scale and projective amplitude are inside curveCoefficients. -/
theorem original_norm_balance (N k : ℕ) (x : Fin N → ℂ) :
    ‖(physicalCompletedFiniteSource k
        (CarrySelfAdjointOperator.PhysicalSewing.finRadialCoefficients N x)).1‖^2-
      ‖(physicalCompletedFiniteSource k
        (CarrySelfAdjointOperator.PhysicalSewing.finRadialCoefficients N x)).2‖^2=
      (fullPair N (fun r => curveQuotient (radialFourSourceStep k) r)
        (curveCoefficients N (radialFourSourceStep k) x)
        (curveCoefficients N (radialFourSourceStep k) x)).re := by
  rw [← curve_eq_original]
  exact curve_norm_balance N _ x

end
end CarryMovingRadial
