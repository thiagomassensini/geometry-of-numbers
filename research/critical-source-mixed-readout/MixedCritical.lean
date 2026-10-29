import SourceCoordinates
import RelativeDeficit

namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Both ordered complex crosses survive before any real scalar readout. -/
theorem chiral_polarized_balance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V C W D : E) :
    inner ℂ (C+Complex.I • V) (D+Complex.I • W) -
      inner ℂ (C-Complex.I • V) (D-Complex.I • W) =
      2*Complex.I*(inner ℂ C W-inner ℂ V D) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  ring

theorem critical_balance_eventually_mixed (s : Fin 2) (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, criticalBalance s n k =
      4*(inner ℂ (sourceValue k (criticalInput s n k) 1)
        (sourceCompanion k (criticalInput s n k) 1)).im := by
  filter_upwards [storage_one_eventually_eq_source_cross (2*(n+1))] with k hk
  rw [criticalBalance_eq_storage]
  exact hk _

/-- Invertibility identifies the coefficient; it gives no sign. -/
theorem critical_mixed_tendsto (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) :
    Tendsto (fun k => (inner ℂ (sourceValue k (criticalInput s n k) 1)
      (sourceCompanion k (criticalInput s n k) 1)).im)
      atTop (nhds (sourceMomentSchur h s.val n/2)) := by
  have ht := (critical_balance_tendsto_of_isUnit s n hA).div_const 4
  have he : 2*sourceMomentSchur h s.val n/4 = sourceMomentSchur h s.val n/2 := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [critical_balance_eventually_mixed s n] with k hk
  rw [hk]
  ring

end
end CarryCriticalMixed
