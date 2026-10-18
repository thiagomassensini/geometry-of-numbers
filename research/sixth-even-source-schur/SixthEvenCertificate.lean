import SourceEnclosures
import FifthOddCertificate

/-! A new even gate only. All arithmetic witnesses below are reduced by
Lean's kernel; no floating point checkpoint is imported. -/
namespace CarrySixthEven
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open GeometryOfNumbers.Analysis CarryMaterialSourceFactorComparison
open Filter
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 96000000

theorem even_six_rectangle_check :
    ∀ r : Fin 6, (sixthEvenRemainderBox r.val r.val r.val).positive = true := by
  decide +kernel

theorem sixth_ordered_even_lower_check :
    ((sixthEvenRemainderBox 5 5 5).add (Box.rat 4 (10^33)).neg).positive = true := by
  decide +kernel

theorem sixth_ordered_even_upper_check :
    ((Box.rat 42 (10^34)).add (sixthEvenRemainderBox 5 5 5).neg).positive = true := by
  decide +kernel

theorem sixth_ordered_even_pivot_bounds :
    (4/10^33:ℝ) < carryPairingPivot (fun i j : ℕ => h (i+j)) 5 ∧
      carryPairingPivot (fun i j : ℕ => h (i+j)) 5 < (42/10^34:ℝ) := by
  have hm := mem_sixthEvenRemainderBox 5 5 5
  have hl := pos_of_mem (mem_add hm (mem_neg (mem_rat 4 (10^33)))) sixth_ordered_even_lower_check
  have hu := pos_of_mem (mem_add (mem_rat 42 (10^34)) (mem_neg hm)) sixth_ordered_even_upper_check
  norm_num only [Int.cast_ofNat,Int.cast_pow] at hl hu
  change (4/10^33:ℝ) < carryPairingRemainder (fun i j : ℕ => h (i+j)) 5 5 5 ∧
    carryPairingRemainder (fun i j : ℕ => h (i+j)) 5 5 5 < (42/10^34:ℝ)
  constructor <;> linarith only [hl,hu]

theorem even_six_pivots_pos (r : ℕ) (hr : r < 6) :
    0 < carryPairingPivot (fun i j : ℕ => h (i+j)) r :=
  pos_of_mem (mem_sixthEvenRemainderBox r r r) (even_six_rectangle_check ⟨r,hr⟩)

theorem even_source_six_posDef : (sourceMomentMatrix h 0 6).PosDef := by
  have hs (i j : ℕ) : (fun i j : ℕ => h (i+j)) i j = (fun i j : ℕ => h (i+j)) j i := by
    simp only [Nat.add_comm]
  have hp := carryPairingCholesky_posDef hs 6 even_six_pivots_pos
  convert hp using 1
  ext i j
  rfl

theorem sixth_even_pivot_pos : 0 < sourceMomentSchur h 0 5 :=
  (sourceMomentMatrix_succ_posDef_iff h 0 5 even_source_five_posDef).mp even_source_six_posDef

theorem sixth_even_criticalMargin : HasCriticalMargin 0 5 :=
  (criticalMargin_iff_pivot 0 5 even_source_five_posDef).mpr sixth_even_pivot_pos

theorem sixth_even_sourceThetaGap_pos : 0 < sourceThetaGap 0 5 :=
  (criticalMargin_iff_thetaGap 0 5 even_source_five_posDef).mp sixth_even_criticalMargin

theorem sixth_even_theta_integral_certificate :
    -4*(Nat.factorial 22:ℝ)*sourceCeiling 0 5 < sourceThetaIntegral 10 :=
  (evenMargin_iff_lower_theta 5 even_source_five_posDef).mp sixth_even_criticalMargin

theorem sixth_even_sourceRemainder_pos : 0 < nativeSourceSchurRemainder 0 5 :=
  (criticalMargin_iff_sourceRemainder 0 5 even_source_five_posDef).mp sixth_even_criticalMargin

/-- The original physical balance has a strictly positive persistent margin
in this critical direction. No bound for the whole twelve-source return. -/
theorem sixth_even_eventually_above_pivot :
    ∀ᶠ k : ℕ in Filter.atTop, sourceMomentSchur h 0 5 < criticalBalance 0 5 k :=
  (tendsto_order.mp (criticalBalance_tendsto 0 5 even_source_five_posDef)).1 _ (by
    have hp := sixth_even_pivot_pos
    change sourceMomentSchur h 0 5 < 2*sourceMomentSchur h 0 5
    linarith)

end
end CarrySixthEven
