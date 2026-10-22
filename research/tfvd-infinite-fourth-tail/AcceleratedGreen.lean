import JetStencils

/-! The accelerated observations still reconstruct the SAME scalar pair of
the original physical Green ledger. All ordered head/tail terms, the signed
companion product and the original dressing derivative remain explicit. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryMaterialParts
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def acceleratedPairHead (M : ℕ) (t : ℝ) : ℂ × ℂ :=
  (Complex.I*baseTwoCanonicalDressingScalar t*acceleratedClockHead M t-
    deriv baseTwoCanonicalDressingScalar t*(1+acceleratedOrdinaryHead M t),
   baseTwoCanonicalDressingScalar t*(1+acceleratedOrdinaryHead M t))

def acceleratedPairTail (M : ℕ) (t : ℝ) : ℂ × ℂ :=
  (Complex.I*baseTwoCanonicalDressingScalar t*acceleratedClockTail M t-
    deriv baseTwoCanonicalDressingScalar t*acceleratedOrdinaryTail M t,
   baseTwoCanonicalDressingScalar t*acceleratedOrdinaryTail M t)

theorem accelerated_pair_head_tail (eta : ℝ) (heta : eta ≠ 0) (M : ℕ) (t : ℝ) :
    carryValveScalarPair eta t = acceleratedPairHead M t+acceleratedPairTail M t := by
  rw [carryValveScalarPair, carryValveCompanionReadout, carryValveValueReadout,
    carryValveSummedSignal_eq eta heta, carryValveSummedClock_eq eta heta]
  apply Prod.ext <;> simp only [acceleratedPairHead, acceleratedPairTail,
    acceleratedClockTail, acceleratedOrdinaryTail, carryValveBeta, Prod.fst_add, Prod.snd_add] <;> ring

/-- Exact original reduced balance, including all three remainder crosses.
This is an observation split; it does not replace the physical source. -/
theorem accelerated_green_tail_ledger (eta : ℝ) (heta : eta ≠ 0) (M L : ℕ) (t u : ℝ) :
    carryValveReducedReturnBalance eta t u-
      reducedCellForm t u (acceleratedPairHead M t) (acceleratedPairHead L u) =
      reducedCellForm t u (acceleratedPairHead M t) (acceleratedPairTail L u)+
      reducedCellForm t u (acceleratedPairTail M t) (acceleratedPairHead L u)+
      reducedCellForm t u (acceleratedPairTail M t) (acceleratedPairTail L u) := by
  rw [reduced_return_cell_form, accelerated_pair_head_tail eta heta M t,
    accelerated_pair_head_tail eta heta L u, reduced_cell_four_terms]
  ring

def dressedValueJetBudget (m M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), ‖rJet j baseTwoCanonicalDressingScalar‖*acceleratedOrdinaryBudget (m-j) M

def dressedCompanionJetBudget (m M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (m+1), ‖rJet j baseTwoCanonicalDressingScalar‖*acceleratedClockBudget (m-j) M)+
    ∑ j ∈ Finset.range (m+1), ‖rJet j (deriv baseTwoCanonicalDressingScalar)‖*acceleratedOrdinaryBudget (m-j) M

theorem accelerated_value_tail_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (fun t => (acceleratedPairTail M t).2)‖ ≤ dressedValueJetBudget m M := by
  exact rJet_mul_bound (baseTwoCanonicalDressingScalar_analyticAt 0)
    (accelerated_ordinary_tail_analytic M) _ (fun j => accelerated_ordinary_jet_bound j M hM) m

theorem accelerated_companion_tail_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (fun t => (acceleratedPairTail M t).1)‖ ≤ dressedCompanionJetBudget m M := by
  have hd := baseTwoCanonicalDressingScalar_analyticAt 0
  change ‖rJet m (fun t => (Complex.I*baseTwoCanonicalDressingScalar t)*acceleratedClockTail M t-
    deriv baseTwoCanonicalDressingScalar t*acceleratedOrdinaryTail M t)‖ ≤ _
  rw [rJet_sub (f:=fun t => (Complex.I*baseTwoCanonicalDressingScalar t)*acceleratedClockTail M t)
    (g:=fun t => deriv baseTwoCanonicalDressingScalar t*acceleratedOrdinaryTail M t)
    ((analyticAt_const.mul hd).mul (accelerated_clock_tail_analytic M))
    (hd.deriv.mul (accelerated_ordinary_tail_analytic M))]
  have hc := rJet_mul_bound (f:=fun t => Complex.I*baseTwoCanonicalDressingScalar t)
    (analyticAt_const.mul hd) (accelerated_clock_tail_analytic M) _
    (fun j => accelerated_clock_jet_bound j M hM) m
  simp only [rJet_left_constant hd, norm_mul, Complex.norm_I, one_mul] at hc
  exact (norm_sub_le _ _).trans (add_le_add hc
    (rJet_mul_bound hd.deriv (accelerated_ordinary_tail_analytic M) _
      (fun j => accelerated_ordinary_jet_bound j M hM) m))
end
end CarryFourthTail
