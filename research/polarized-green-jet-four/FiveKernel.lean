import JetFourSource

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen
open CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192

/-- Coefficient products only, after the original vector synthesis. -/
def crosses (u v : Fin 3 → ℝ) : ℕ → ℝ
  | 0 => u 0*v 0
  | 1 => u 0*v 1+u 1*v 0
  | 2 => u 0*v 2+u 2*v 0
  | 3 => u 1*v 1
  | 4 => u 1*v 2+u 2*v 1
  | _ => u 2*v 2

def sampleMass (K : ℝ) (u v : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![K^9*crosses u v 5/8640-7*K^7*crosses u v 4/2880+
      K^5*(crosses u v 2/45+crosses u v 3/24)-7*K^3*crosses u v 1/24+K*crosses u v 0,
    -K^9*crosses u v 5/7560+K^7*crosses u v 4/315+
      K^5*(-crosses u v 2/18-crosses u v 3/30)+K^3*crosses u v 1/3,
    K^9*crosses u v 5/13440-29*K^7*crosses u v 4/13440+
      K^5*(crosses u v 2/16+crosses u v 3/120)-K^3*crosses u v 1/8,
    -K^9*crosses u v 5/45360+K^7*crosses u v 4/1260-K^5*crosses u v 2/30,
    K^9*crosses u v 5/362880-K^7*crosses u v 4/8064+K^5*crosses u v 2/144]

/-- All three non-isotropic sectors, with INDEPENDENT arguments. -/
def quarticBalance (η : ℝ) (u v : Fin 3 → ℝ) (k : ℕ) : ℝ :=
  (physicalForm (quarticBulk η k u) (quarticBulk η k v)).re+
  (physicalForm (quarticBulk η k u) (quarticResidual η k v)).re+
  (physicalForm (quarticResidual η k u) (quarticBulk η k v)).re

theorem quartic_balance_source (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hr : fiveRegular k) (u v : Fin 3 → ℝ) : quarticBalance η u v k=
      (physicalForm (completedSource k (quarticInput k u)) (completedSource k (quarticInput k v))).re := by
  rw [quartic_full_green η hη0 hη1,quartic_residual_cross_zero η hη0.ne' k hr]
  simp only [quarticBalance,Complex.add_re,add_zero]

theorem quartic_balance_twenty_five (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hr : fiveRegular k) (u v : Fin 3 → ℝ) : quarticBalance η u v k=
      ∑ i : Fin 5, ∑ j : Fin 5, fiveWeight k u i*fiveWeight k v j*
        (((k : ℝ)+1)*((nativeResponse (canonicalCompletedC3RadialTiltPoint k i)).im+
        (nativeResponse (canonicalCompletedC3RadialTiltPoint k j)).im)/((i : ℝ)+(j : ℝ)+2)) := by
  rw [quartic_balance_source η hη0 hη1 k hr,quartic_input_five,quartic_input_five]
  simp only [map_sum,map_smul]
  rw [physical_form_sum]
  simp only [Complex.re_sum]
  simp_rw [real_weighted_form]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [source_basis_real k i j (hr ⟨i,by omega⟩).1 (hr ⟨i,by omega⟩).2
    (hr ⟨j,by omega⟩).1 (hr ⟨j,by omega⟩).2]

theorem quartic_balance_five_samples (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hr : fiveRegular k) (u v : Fin 3 → ℝ) : quarticBalance η u v k=
      ∑ j : Fin 5, sampleMass ((k : ℝ)+1) u v j*
        (nativeResponse (canonicalCompletedC3RadialTiltPoint k j)).im := by
  rw [quartic_balance_twenty_five η hη0 hη1 k hr]
  norm_num [Fin.sum_univ_succ,fiveWeight,sampleMass,crosses]
  ring

end
end CarryPolarizedFour
