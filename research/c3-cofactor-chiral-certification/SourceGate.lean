import IntervalGate
import SchurGate

namespace C3Cofactor

noncomputable section
set_option autoImplicit false

def sourceOddA (c : Fin 7 → ℝ) : ℝ := c 1 * c 1 - 2 * (c 0 * c 2)
def sourceOddB (c : Fin 7 → ℝ) : ℝ := c 1 * c 2 - 3 * (c 0 * c 3)
def sourceOddD (c : Fin 7 → ℝ) : ℝ :=
  (2 * (c 2 * c 2) - 2 * (c 1 * c 3)) - 4 * (c 0 * c 4)
def sourceOddE (c : Fin 7 → ℝ) : ℝ := c 1 * c 3 - 4 * (c 0 * c 4)
def sourceOddF (c : Fin 7 → ℝ) : ℝ :=
  (2 * (c 2 * c 3) - 3 * (c 1 * c 4)) - 5 * (c 0 * c 5)
def sourceOddG (c : Fin 7 → ℝ) : ℝ :=
  ((3 * (c 3 * c 3) - 2 * (c 2 * c 4)) - 4 * (c 1 * c 5)) - 6 * (c 0 * c 6)

theorem RationalBall.lower_le_of_contains {b : RationalBall} {x : ℝ}
    (h : b.Contains x) : b.center - b.radius ≤ x := by
  have hl := (abs_le.mp h).1
  change ((b.center : ℝ) - (b.radius : ℝ)) ≤ x
  change -((b.radius : ℝ)) ≤ x - (b.center : ℝ) at hl
  linarith

theorem sourceOddA_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddABall.Contains (sourceOddA c) := by
  unfold oddABall sourceOddA
  exact RationalBall.sub_contains
    (RationalBall.mul_contains (hc 1) (hc 1))
    (RationalBall.mul_contains (RationalBall.point_contains 2)
      (RationalBall.mul_contains (hc 0) (hc 2)))

theorem sourceOddB_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddBBall.Contains (sourceOddB c) := by
  unfold oddBBall sourceOddB
  exact RationalBall.sub_contains
    (RationalBall.mul_contains (hc 1) (hc 2))
    (RationalBall.mul_contains (RationalBall.point_contains 3)
      (RationalBall.mul_contains (hc 0) (hc 3)))

theorem sourceOddD_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddDBall.Contains (sourceOddD c) := by
  unfold oddDBall sourceOddD
  apply RationalBall.sub_contains
  · apply RationalBall.sub_contains
    · exact RationalBall.mul_contains (RationalBall.point_contains 2)
        (RationalBall.mul_contains (hc 2) (hc 2))
    · exact RationalBall.mul_contains (RationalBall.point_contains 2)
        (RationalBall.mul_contains (hc 1) (hc 3))
  · exact RationalBall.mul_contains (RationalBall.point_contains 4)
      (RationalBall.mul_contains (hc 0) (hc 4))

theorem sourceOddE_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddEBall.Contains (sourceOddE c) := by
  unfold oddEBall sourceOddE
  exact RationalBall.sub_contains
    (RationalBall.mul_contains (hc 1) (hc 3))
    (RationalBall.mul_contains (RationalBall.point_contains 4)
      (RationalBall.mul_contains (hc 0) (hc 4)))

theorem sourceOddF_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddFBall.Contains (sourceOddF c) := by
  unfold oddFBall sourceOddF
  apply RationalBall.sub_contains
  · apply RationalBall.sub_contains
    · exact RationalBall.mul_contains (RationalBall.point_contains 2)
        (RationalBall.mul_contains (hc 2) (hc 3))
    · exact RationalBall.mul_contains (RationalBall.point_contains 3)
        (RationalBall.mul_contains (hc 1) (hc 4))
  · exact RationalBall.mul_contains (RationalBall.point_contains 5)
      (RationalBall.mul_contains (hc 0) (hc 5))

theorem sourceOddG_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddGBall.Contains (sourceOddG c) := by
  unfold oddGBall sourceOddG
  apply RationalBall.sub_contains
  · apply RationalBall.sub_contains
    · apply RationalBall.sub_contains
      · exact RationalBall.mul_contains (RationalBall.point_contains 3)
          (RationalBall.mul_contains (hc 3) (hc 3))
      · exact RationalBall.mul_contains (RationalBall.point_contains 2)
          (RationalBall.mul_contains (hc 2) (hc 4))
    · exact RationalBall.mul_contains (RationalBall.point_contains 4)
        (RationalBall.mul_contains (hc 1) (hc 5))
  · exact RationalBall.mul_contains (RationalBall.point_contains 6)
      (RationalBall.mul_contains (hc 0) (hc 6))

theorem sourceOddPrefix_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddPrefixBall.Contains (oddPrefixDet (sourceOddA c) (sourceOddB c) (sourceOddD c)) := by
  unfold oddPrefixBall oddPrefixDet
  exact RationalBall.sub_contains
    (RationalBall.mul_contains (sourceOddA_contains hc) (sourceOddD_contains hc))
    (by simpa [pow_two] using
      RationalBall.mul_contains (sourceOddB_contains hc) (sourceOddB_contains hc))

theorem sourceOddR0_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddR0Ball.Contains
      (oddResidual0 (sourceOddA c) (sourceOddB c) (sourceOddE c)
        refXBall.center refYBall.center) := by
  unfold oddR0Ball oddResidual0
  have hx : refXBall.Contains (refXBall.center : ℝ) := by
    change |(refXBall.center : ℝ) - (refXBall.center : ℝ)| ≤ (refXBall.radius : ℝ)
    norm_num [refXBall, RationalBall.point]
  have hy : refYBall.Contains (refYBall.center : ℝ) := by
    change |(refYBall.center : ℝ) - (refYBall.center : ℝ)| ≤ (refYBall.radius : ℝ)
    norm_num [refYBall, RationalBall.point]
  exact RationalBall.add_contains
    (RationalBall.add_contains
      (RationalBall.mul_contains (sourceOddA_contains hc) hx)
      (RationalBall.mul_contains (sourceOddB_contains hc) hy))
    (sourceOddE_contains hc)

theorem sourceOddR1_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddR1Ball.Contains
      (oddResidual1 (sourceOddB c) (sourceOddD c) (sourceOddF c)
        refXBall.center refYBall.center) := by
  unfold oddR1Ball oddResidual1
  have hx : refXBall.Contains (refXBall.center : ℝ) := by
    change |(refXBall.center : ℝ) - (refXBall.center : ℝ)| ≤ (refXBall.radius : ℝ)
    norm_num [refXBall, RationalBall.point]
  have hy : refYBall.Contains (refYBall.center : ℝ) := by
    change |(refYBall.center : ℝ) - (refYBall.center : ℝ)| ≤ (refYBall.radius : ℝ)
    norm_num [refYBall, RationalBall.point]
  exact RationalBall.add_contains
    (RationalBall.add_contains
      (RationalBall.mul_contains (sourceOddB_contains hc) hx)
      (RationalBall.mul_contains (sourceOddD_contains hc) hy))
    (sourceOddF_contains hc)

theorem sourceOddEnergy_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddEnergyBall.Contains
      (oddDirectionEnergy (sourceOddA c) (sourceOddB c) (sourceOddD c)
        (sourceOddE c) (sourceOddF c) (sourceOddG c)
        refXBall.center refYBall.center) := by
  unfold oddEnergyBall oddDirectionEnergy
  have hx : refXBall.Contains (refXBall.center : ℝ) := by
    change |(refXBall.center : ℝ) - (refXBall.center : ℝ)| ≤ (refXBall.radius : ℝ)
    norm_num [refXBall, RationalBall.point]
  have hy : refYBall.Contains (refYBall.center : ℝ) := by
    change |(refYBall.center : ℝ) - (refYBall.center : ℝ)| ≤ (refYBall.radius : ℝ)
    norm_num [refYBall, RationalBall.point]
  have h2 := RationalBall.point_contains 2
  have hax2 : (oddABall.mul (refXBall.mul refXBall)).Contains
      (sourceOddA c * refXBall.center ^ 2) := by
    simpa [pow_two] using
      RationalBall.mul_contains (sourceOddA_contains hc)
        (RationalBall.mul_contains hx hx)
  have h2bxy : ((RationalBall.point 2).mul ((oddBBall.mul refXBall).mul refYBall)).Contains
      (2 * (sourceOddB c * refXBall.center) * refYBall.center) := by
    simpa [mul_assoc] using RationalBall.mul_contains h2
      (RationalBall.mul_contains
        (RationalBall.mul_contains (sourceOddB_contains hc) hx) hy)
  have hdy2 : (oddDBall.mul (refYBall.mul refYBall)).Contains
      (sourceOddD c * refYBall.center ^ 2) := by
    simpa [pow_two] using
      RationalBall.mul_contains (sourceOddD_contains hc)
        (RationalBall.mul_contains hy hy)
  have h2ex : ((RationalBall.point 2).mul (oddEBall.mul refXBall)).Contains
      (2 * (sourceOddE c * refXBall.center)) := by
    exact RationalBall.mul_contains h2
      (RationalBall.mul_contains (sourceOddE_contains hc) hx)
  have h2fy : ((RationalBall.point 2).mul (oddFBall.mul refYBall)).Contains
      (2 * (sourceOddF c * refYBall.center)) := by
    exact RationalBall.mul_contains h2
      (RationalBall.mul_contains (sourceOddF_contains hc) hy)
  have hterms :
      ((((((oddABall.mul (refXBall.mul refXBall)).add
        ((RationalBall.point 2).mul ((oddBBall.mul refXBall).mul refYBall))).add
        (oddDBall.mul (refYBall.mul refYBall))).add
        ((RationalBall.point 2).mul (oddEBall.mul refXBall))).add
        ((RationalBall.point 2).mul (oddFBall.mul refYBall))).add oddGBall).Contains
        (sourceOddA c * refXBall.center ^ 2 +
          2 * (sourceOddB c * refXBall.center) * refYBall.center +
          sourceOddD c * refYBall.center ^ 2 +
          2 * (sourceOddE c * refXBall.center) +
          2 * (sourceOddF c * refYBall.center) + sourceOddG c) := by
    apply RationalBall.add_contains
    · apply RationalBall.add_contains
      · apply RationalBall.add_contains
        · apply RationalBall.add_contains
          · exact RationalBall.add_contains hax2 h2bxy
          · exact hdy2
        · exact h2ex
      · exact h2fy
    · exact sourceOddG_contains hc
  simpa [oddDirectionEnergy, mul_assoc] using hterms

theorem sourceOddAdjugate_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddAdjugateResidualBall.Contains
      (oddAdjugateResidual (sourceOddA c) (sourceOddB c) (sourceOddD c)
        (sourceOddE c) (sourceOddF c) refXBall.center refYBall.center) := by
  unfold oddAdjugateResidualBall oddAdjugateResidual
  have h2 := RationalBall.point_contains 2
  have hr0sq : (RationalBall.mul oddR0Ball oddR0Ball).Contains
      (oddResidual0 (sourceOddA c) (sourceOddB c) (sourceOddE c)
        refXBall.center refYBall.center ^ 2) := by
    simpa [pow_two] using
      RationalBall.mul_contains (sourceOddR0_contains hc) (sourceOddR0_contains hc)
  have hr1sq : (RationalBall.mul oddR1Ball oddR1Ball).Contains
      (oddResidual1 (sourceOddB c) (sourceOddD c) (sourceOddF c)
        refXBall.center refYBall.center ^ 2) := by
    simpa [pow_two] using
      RationalBall.mul_contains (sourceOddR1_contains hc) (sourceOddR1_contains hc)
  have hcross : ((RationalBall.point 2).mul
        (oddBBall.mul (oddR0Ball.mul oddR1Ball))).Contains
      (2 * (sourceOddB c * (oddResidual0 (sourceOddA c) (sourceOddB c)
        (sourceOddE c) refXBall.center refYBall.center *
        oddResidual1 (sourceOddB c) (sourceOddD c) (sourceOddF c)
          refXBall.center refYBall.center))) := by
    exact RationalBall.mul_contains h2
      (RationalBall.mul_contains (sourceOddB_contains hc)
        (RationalBall.mul_contains (sourceOddR0_contains hc) (sourceOddR1_contains hc)))
  exact RationalBall.add_contains
    (RationalBall.sub_contains
      (RationalBall.mul_contains (sourceOddD_contains hc)
        hr0sq)
      (by simpa [mul_assoc] using hcross))
    (RationalBall.mul_contains (sourceOddA_contains hc)
      hr1sq)

theorem sourceOddMargin_contains {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    oddCofactorMarginBall.Contains
      (oddPrefixDet (sourceOddA c) (sourceOddB c) (sourceOddD c) *
        oddDirectionEnergy (sourceOddA c) (sourceOddB c) (sourceOddD c)
          (sourceOddE c) (sourceOddF c) (sourceOddG c)
          refXBall.center refYBall.center -
        oddAdjugateResidual (sourceOddA c) (sourceOddB c) (sourceOddD c)
          (sourceOddE c) (sourceOddF c) refXBall.center refYBall.center) := by
  unfold oddCofactorMarginBall
  exact RationalBall.sub_contains
    (RationalBall.mul_contains (sourceOddPrefix_contains hc) (sourceOddEnergy_contains hc))
    (sourceOddAdjugate_contains hc)

/-- The rational interval evaluation is a conditional source certificate: if
the seven original coefficients lie in the displayed rational boxes, then the
odd prefix and its exact cofactor margin are strictly positive. -/
theorem candidate_source_gate {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    0 < sourceOddA c ∧
      0 < oddPrefixDet (sourceOddA c) (sourceOddB c) (sourceOddD c) ∧
      0 < oddPrefixDet (sourceOddA c) (sourceOddB c) (sourceOddD c) *
        oddDirectionEnergy (sourceOddA c) (sourceOddB c) (sourceOddD c)
          (sourceOddE c) (sourceOddF c) (sourceOddG c)
          refXBall.center refYBall.center -
        oddAdjugateResidual (sourceOddA c) (sourceOddB c) (sourceOddD c)
          (sourceOddE c) (sourceOddF c) refXBall.center refYBall.center := by
  have ha := RationalBall.lower_le_of_contains (sourceOddA_contains hc)
  have hD := RationalBall.lower_le_of_contains (sourceOddPrefix_contains hc)
  have hmargin := RationalBall.lower_le_of_contains (sourceOddMargin_contains hc)
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by exact_mod_cast candidate_oddA_lower_positive) ha
  · exact lt_of_lt_of_le (by exact_mod_cast candidate_oddPrefix_lower_positive) hD
  · exact lt_of_lt_of_le (by exact_mod_cast candidate_cofactor_margin_lower_positive) hmargin

/-- If future source analysis proves the seven coefficient boxes, this gate
immediately certifies positive definiteness of the original odd 3×3 block. -/
theorem source_odd_block_posDef_of_coefficient_boxes {c : Fin 7 → ℝ}
    (hc : ∀ j, (candidateCoefficientBall j).Contains (c j)) :
    (oddThirdB (sourceOddA c) (sourceOddB c) (sourceOddD c)
      (sourceOddE c) (sourceOddF c) (sourceOddG c)).PosDef := by
  obtain ⟨ha, hD, hmargin⟩ := candidate_source_gate hc
  exact odd_third_posDef_of_cofactor_gate
    (sourceOddA c) (sourceOddB c) (sourceOddD c)
    (sourceOddE c) (sourceOddF c) (sourceOddG c)
    refXBall.center refYBall.center ha hD hmargin

#print axioms candidate_source_gate
#print axioms source_odd_block_posDef_of_coefficient_boxes

end
end C3Cofactor
