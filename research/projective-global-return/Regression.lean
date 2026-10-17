import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen
import GeometryOfNumbers.Analysis.CompleteVerticalObservationGram
import GeometryOfNumbers.Analysis.CompletedClockCandidateObstructions

open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open Filter
open scoped ComplexConjugate Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

-- Eta is the existing critical vertical amplitude, never fitted to a moment.
example (t : ℝ) : HasSum
    (carryValveCell (criticalVerticalAmplitudeRatio 2 (by decide))
      (baseTwoCompletedBoundaryHilbertState t)) (carryValveBeta t) :=
  carryValveReturn_source _ (criticalVerticalAmplitudeRatio_pos 2 _).ne' t

-- The output's boundary relation requires no assertion L(Y) ∈ domain(L).
example (eta : ℝ) (heta : eta ≠ 0) (y : completedBoundaryTransportedClock.domain) :
    HasSum (carryValveCell eta (completedBoundaryTransportedClock y))
      (completedBoundaryTransportedClock y).snd.snd := carryValveReturn_clock_graph eta heta y

-- Exact material edge canary; clock connection remains log4-log3 at edge2.
example (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveEdge eta (baseTwoCompletedBoundaryHilbertState t) 0 0 = criticalMaterialGradient t 2 := by
  rw [carryValveEdge_eq eta heta]
  rfl

example (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveEdge eta (completedBoundaryTransportedClock (carryValveSource t)) 0 0 =
      (Real.log (4 : ℝ) : ℂ) * criticalMaterialSample t 4 -
        (Real.log (3 : ℝ) : ℂ) * criticalMaterialSample t 3 := by
  rw [carryValveEdge_clock eta heta]
  exact baseTwoCompletedBoundaryHilbertClockCoordinate_eq t 2

-- Old 72 correction has its exact two material edge indices, not depth indices.
example (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveEdge eta (baseTwoCompletedBoundaryHilbertState t) 19 1 -
      carryValveEdge eta (baseTwoCompletedBoundaryHilbertState t) 15 0 =
        criticalMaterialGradient t 79 - criticalMaterialGradient t 62 := by
  rw [carryValveEdge_eq eta heta, carryValveEdge_eq eta heta]
  rfl

-- M=0 must retain the entire ordinary and clocked tail.
example (eta t : ℝ) :
    carryValveReturnTail eta (baseTwoCompletedBoundaryHilbertState t) 0 = carryValveBeta t := by
  simp [carryValveReturnTail, carryValveReturnPrefix, carryMaterialProjectiveEncode, carryValveBeta]

example (eta t : ℝ) :
    carryValveReturnTail eta (completedBoundaryTransportedClock (carryValveSource t)) 0 = carryValveKappa t := by
  simp [carryValveReturnTail, carryValveReturnPrefix, carryMaterialProjectiveEncode,
    carryValveKappa, carryValveSource]

-- Unequal cutoffs and distinct times in the actual oriented cell polarization.
example (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    conj (carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) 1) *
        carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState u) 2 =
      conj (baseTwoCriticalCenterCell t 0) *
        (baseTwoCriticalCenterCell u 0 + baseTwoCriticalCenterCell u 1) := by
  simp only [carryValveReturnPrefix, carryValveCell_source eta heta]
  simp [Finset.sum_range_succ]

-- Complex imaginary polarization keeps cross quadratures and their sign.
example (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) :
    (conj (carryValveEdge eta (baseTwoCompletedBoundaryHilbertState t) 0 0) *
      carryValveEdge eta (baseTwoCompletedBoundaryHilbertState u) 3 0).im =
      carryValveRealCross eta h0 h1 (baseTwoCompletedBoundaryHilbertState t)
        (baseTwoCompletedBoundaryHilbertState u) (0,0) (3,0) 0 1 -
      carryValveRealCross eta h0 h1 (baseTwoCompletedBoundaryHilbertState t)
        (baseTwoCompletedBoundaryHilbertState u) (0,0) (3,0) 1 0 := by
  exact congrArg Complex.im (carryValveEdge_polarized eta h0 h1
    (baseTwoCompletedBoundaryHilbertState t) (baseTwoCompletedBoundaryHilbertState u) (0,0) (3,0))

-- The same real-limit product includes clocked sources in both arguments.
example (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource t)) p.1) *
        carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource u)) p.2)
      (atTop ×ˢ atTop) (nhds (conj (carryValveKappa t)*carryValveKappa u)) :=
  carryValveReturn_clock_product_tendsto eta heta t u

-- Prefix=0 gives a seed-only F and its actual dressing companion, not zero.
example (eta t : ℝ) : carryValvePrefixValue eta 0 t = baseTwoCanonicalDressingScalar t := by
  simp [carryValvePrefixValue, carryValveReturnPrefix]

example (eta t : ℝ) : carryValvePrefixCompanion eta 0 t = -deriv baseTwoCanonicalDressingScalar t := by
  simp [carryValvePrefixCompanion, carryValveReturnPrefix]

-- No division even where t=0, u=0, or u=t.
example (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair t) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
        (carryMaterialPairComplement (carryMaterialReducedCompanionPair t)) =
      carryValveReducedReturnBalance eta t t := carryValveReducedReturnBalance_physical eta heta t t

#check carryMaterialClock_reduced_green_ledger
#check completedBoundaryTransportedClock_not_standard_symmetric
#check completedClock_isometric_intertwiner_impossible
#check completeCriticalVerticalObservabilityGram_not_canonicalHankel
#check carryMaterialProjective_source_return_invisible

end
