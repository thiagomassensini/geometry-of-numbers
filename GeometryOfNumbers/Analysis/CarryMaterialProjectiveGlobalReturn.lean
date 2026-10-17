import GeometryOfNumbers.Analysis.CarryMaterialTfvdProjectiveTransport
import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling
import Mathlib.Order.Filter.AtTopBot.Prod

/-! # Global return and its polarization in the existing valve coordinates

Only encoded physical incidences are reconstructed. The graph relation comes
from the ORIGINAL clock domain; no constraint is imposed on an arbitrary
ledger. Clock outputs use their proved boundary relation, not an iterated domain.
No separate infinite Green/trace sums or positive Gram are asserted.
-/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion C2GlobalGreenBridge RealCarry Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Two reconstructed real quadratures at the decoded physical edge. -/
def carryValveEdge (eta : ℝ) (y : MaterialCarrier) (k : ℕ) (s : Fin 2) : ℂ :=
  realPlaneToComplexIsometry (realPlaneHilbertEquiv
    (carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y)
        (baseTwoPhysicalEdgeC2Address (k,s)) 0,
     carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y)
        (baseTwoPhysicalEdgeC2Address (k,s)) 1))

theorem carryValveEdge_eq (eta : ℝ) (heta : eta ≠ 0) (y : MaterialCarrier)
    (k : ℕ) (s : Fin 2) :
    carryValveEdge eta y k s = y.snd.fst (baseTwoPhysicalEdgeIndex (k,s)) := by
  unfold carryValveEdge
  rw [carryMaterialProjective_coordinate_encode eta heta,
    carryMaterialProjective_coordinate_encode eta heta]
  have he (v : RealPlaneHilbert) : realPlaneHilbertEquiv (v 0,v 1) = v := by
    ext r
    fin_cases r <;> rfl
  rw [he, baseTwoPhysicalEdgeC2State_apply_edge, baseTwoMaterialEdgeRealification_pack]

def carryValveCell (eta : ℝ) (y : MaterialCarrier) (k : ℕ) : ℂ :=
  carryValveEdge eta y k 1 - carryValveEdge eta y k 0

theorem carryValveCell_eq (eta : ℝ) (heta : eta ≠ 0) (y : MaterialCarrier) :
    carryValveCell eta y = completedBoundaryCellReturnCoordinates y := by
  funext k
  rw [carryValveCell, carryValveEdge_eq eta heta, carryValveEdge_eq eta heta]
  rfl

/-- The original domain supplies this relation, not a new ledger hypothesis. -/
theorem carryValveReturn_graph (eta : ℝ) (heta : eta ≠ 0)
    (y : completedBoundaryTransportedClock.domain) :
    HasSum (carryValveCell eta y.val) (carryMaterialProjectiveEncode eta y.val).globalReturn := by
  rw [carryValveCell_eq eta heta]
  exact y.property.1

/-- The image has its boundary relation without a second-order clock domain. -/
theorem carryValveReturn_clock_graph (eta : ℝ) (heta : eta ≠ 0)
    (y : completedBoundaryTransportedClock.domain) :
    HasSum (carryValveCell eta (completedBoundaryTransportedClock y))
      (carryMaterialProjectiveEncode eta (completedBoundaryTransportedClock y)).globalReturn := by
  rw [carryValveCell_eq eta heta]
  exact completedBoundaryTransportedClock_image_boundary y

def carryValveSource (t : ℝ) : completedBoundaryTransportedClock.domain :=
  ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩

def carryValveBeta (t : ℝ) : ℂ := baseTwoCompletedBoundaryValue t

def carryValveKappa (t : ℝ) : ℂ :=
  baseTwoCompletedBoundaryClockReturn (baseTwoCompletedBoundaryHilbertState t)

theorem carryValveCell_source (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) (k : ℕ) :
    carryValveCell eta (baseTwoCompletedBoundaryHilbertState t) k = baseTwoCriticalCenterCell t k := by
  rw [carryValveCell_eq eta heta, baseTwoCriticalCenterCell_eq_gradientEdges]
  rfl

theorem carryValveReturn_source (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    HasSum (carryValveCell eta (baseTwoCompletedBoundaryHilbertState t)) (carryValveBeta t) :=
  carryValveReturn_graph eta heta (carryValveSource t)

theorem carryValveReturn_clock_source (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    HasSum (carryValveCell eta (completedBoundaryTransportedClock (carryValveSource t)))
      (carryValveKappa t) :=
  carryValveReturn_clock_graph eta heta (carryValveSource t)

theorem carryValveBeta_eq_tsum (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveBeta t = ∑' k, carryValveCell eta (baseTwoCompletedBoundaryHilbertState t) k :=
  (carryValveReturn_source eta heta t).tsum_eq.symm

theorem carryValveKappa_eq_tsum (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveKappa t = ∑' k, carryValveCell eta (completedBoundaryTransportedClock (carryValveSource t)) k :=
  (carryValveReturn_clock_source eta heta t).tsum_eq.symm

/-- The existing log(n+2)-log(n+1) connection remains in this coordinate. -/
theorem carryValveEdge_clock (eta : ℝ) (heta : eta ≠ 0)
    (y : completedBoundaryTransportedClock.domain) (k : ℕ) (s : Fin 2) :
    carryValveEdge eta (completedBoundaryTransportedClock y) k s =
      baseTwoCompletedBoundaryHilbertClockCoordinate y.val (baseTwoPhysicalEdgeIndex (k,s)) := by
  rw [carryValveEdge_eq eta heta]
  rfl

/-- Finite oriented cell polarization: the two edges keep their own addresses. -/
theorem carryValveCell_polarized (eta : ℝ) (y z : MaterialCarrier) (k l : ℕ) :
    conj (carryValveCell eta y k) * carryValveCell eta z l =
      conj (carryValveEdge eta y k 1) * carryValveEdge eta z l 1 -
      conj (carryValveEdge eta y k 1) * carryValveEdge eta z l 0 -
      conj (carryValveEdge eta y k 0) * carryValveEdge eta z l 1 +
      conj (carryValveEdge eta y k 0) * carryValveEdge eta z l 0 := by
  simp only [carryValveCell, map_sub]
  ring

/-- The existing four real TFVD crossings, at independently decoded edges. -/
def carryValveRealCross (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (e f : BaseTwoPhysicalEdge) (r s : Fin 2) : ℝ :=
  let i := baseTwoPhysicalEdgeC2Address e
  let j := baseTwoPhysicalEdgeC2Address f
  carryMaterialTfvdGreenReadout eta i r y.snd.fst * carryMaterialTfvdGreenReadout eta j s z.snd.fst +
  carryMaterialTfvdGreenReadout eta i r y.snd.fst * carryMaterialTfvdReturnReadout eta h0 h1 j s z.snd.fst +
  carryMaterialTfvdReturnReadout eta h0 h1 i r y.snd.fst * carryMaterialTfvdGreenReadout eta j s z.snd.fst +
  carryMaterialTfvdReturnReadout eta h0 h1 i r y.snd.fst *
    carryMaterialTfvdReturnReadout eta h0 h1 j s z.snd.fst

theorem carryValveRealCross_eq (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (e f : BaseTwoPhysicalEdge) (r s : Fin 2) :
    carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y)
        (baseTwoPhysicalEdgeC2Address e) r *
      carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta z)
        (baseTwoPhysicalEdgeC2Address f) s = carryValveRealCross eta h0 h1 y z e f r s :=
  carryMaterialProjective_crossings eta h0 h1 y z _ _ r s

/-- Both the real and imaginary part of the complex product, including all
four TFVD crossings for each ordered quadrature pair. -/
theorem carryValveEdge_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (e f : BaseTwoPhysicalEdge) :
    conj (carryValveEdge eta y e.1 e.2) * carryValveEdge eta z f.1 f.2 =
      Complex.mk
        (carryValveRealCross eta h0 h1 y z e f 0 0 + carryValveRealCross eta h0 h1 y z e f 1 1)
        (carryValveRealCross eta h0 h1 y z e f 0 1 - carryValveRealCross eta h0 h1 y z e f 1 0) := by
  simp only [← carryValveRealCross_eq eta h0 h1]
  change conj (Complex.mk
    (carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y) (baseTwoPhysicalEdgeC2Address e) 0)
    (carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y) (baseTwoPhysicalEdgeC2Address e) 1)) *
    Complex.mk
    (carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta z) (baseTwoPhysicalEdgeC2Address f) 0)
    (carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta z) (baseTwoPhysicalEdgeC2Address f) 1) = _
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  <;> ring

/-- A finite ordered edge product retaining all quadratures and TFVD terms. -/
def carryValveComplexCross (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (e f : BaseTwoPhysicalEdge) : ℂ :=
  Complex.mk
    (carryValveRealCross eta h0 h1 y z e f 0 0 + carryValveRealCross eta h0 h1 y z e f 1 1)
    (carryValveRealCross eta h0 h1 y z e f 0 1 - carryValveRealCross eta h0 h1 y z e f 1 0)

/-- Four oriented edge pairs, each with all four Green/trace crossings and
both complex quadratures. No common C2 fiber for the two sides is assumed. -/
theorem carryValveCell_tfvd_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (k l : ℕ) :
    conj (carryValveCell eta y k) * carryValveCell eta z l =
      carryValveComplexCross eta h0 h1 y z (k,1) (l,1) -
      carryValveComplexCross eta h0 h1 y z (k,1) (l,0) -
      carryValveComplexCross eta h0 h1 y z (k,0) (l,1) +
      carryValveComplexCross eta h0 h1 y z (k,0) (l,0) := by
  unfold carryValveComplexCross
  rw [carryValveCell_polarized,
    carryValveEdge_polarized eta h0 h1 y z (k,1) (l,1),
    carryValveEdge_polarized eta h0 h1 y z (k,1) (l,0),
    carryValveEdge_polarized eta h0 h1 y z (k,0) (l,1),
    carryValveEdge_polarized eta h0 h1 y z (k,0) (l,0)]

def carryValveReturnPrefix (eta : ℝ) (y : MaterialCarrier) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.range M, carryValveCell eta y k

def carryValveReturnTail (eta : ℝ) (y : MaterialCarrier) (M : ℕ) : ℂ :=
  (carryMaterialProjectiveEncode eta y).globalReturn - carryValveReturnPrefix eta y M

theorem carryValveReturnPrefix_polarized (eta : ℝ) (y z : MaterialCarrier) (M N : ℕ) :
    conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N =
      ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N,
        conj (carryValveCell eta y k) * carryValveCell eta z l := by
  simp only [carryValveReturnPrefix, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem carryValveReturnPrefix_oriented (eta : ℝ) (y z : MaterialCarrier) (M N : ℕ) :
    conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N =
      ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N,
        (conj (carryValveEdge eta y k 1)*carryValveEdge eta z l 1 -
         conj (carryValveEdge eta y k 1)*carryValveEdge eta z l 0 -
         conj (carryValveEdge eta y k 0)*carryValveEdge eta z l 1 +
         conj (carryValveEdge eta y k 0)*carryValveEdge eta z l 0) := by
  rw [carryValveReturnPrefix_polarized]
  simp only [carryValveCell_polarized]

theorem carryValveReturnPrefix_tfvd (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : MaterialCarrier) (M N : ℕ) :
    conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N =
      ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N,
        (carryValveComplexCross eta h0 h1 y z (k,1) (l,1) -
         carryValveComplexCross eta h0 h1 y z (k,1) (l,0) -
         carryValveComplexCross eta h0 h1 y z (k,0) (l,1) +
         carryValveComplexCross eta h0 h1 y z (k,0) (l,0)) := by
  rw [carryValveReturnPrefix_polarized]
  simp only [carryValveCell_tfvd_polarized eta h0 h1]

/-- Independent prefix-prefix, prefix-tail, tail-prefix and tail-tail terms. -/
theorem carryValveReturn_tail_ledger (eta : ℝ) (y z : MaterialCarrier) (M N : ℕ) :
    conj (carryMaterialProjectiveEncode eta y).globalReturn *
        (carryMaterialProjectiveEncode eta z).globalReturn =
      conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N +
      conj (carryValveReturnPrefix eta y M) * carryValveReturnTail eta z N +
      conj (carryValveReturnTail eta y M) * carryValveReturnPrefix eta z N +
      conj (carryValveReturnTail eta y M) * carryValveReturnTail eta z N := by
  simp only [carryValveReturnTail, map_sub]
  ring

theorem carryValveReturn_product_error (eta : ℝ) (y z : MaterialCarrier) (M N : ℕ) :
    ‖conj (carryMaterialProjectiveEncode eta y).globalReturn *
        (carryMaterialProjectiveEncode eta z).globalReturn -
        conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N‖ ≤
      ‖carryValveReturnPrefix eta y M‖ * ‖carryValveReturnTail eta z N‖ +
      ‖carryValveReturnTail eta y M‖ * ‖carryValveReturnPrefix eta z N‖ +
      ‖carryValveReturnTail eta y M‖ * ‖carryValveReturnTail eta z N‖ := by
  have h := carryValveReturn_tail_ledger eta y z M N
  have he : conj (carryMaterialProjectiveEncode eta y).globalReturn *
      (carryMaterialProjectiveEncode eta z).globalReturn -
      conj (carryValveReturnPrefix eta y M) * carryValveReturnPrefix eta z N =
      (conj (carryValveReturnPrefix eta y M) * carryValveReturnTail eta z N +
       conj (carryValveReturnTail eta y M) * carryValveReturnPrefix eta z N) +
       conj (carryValveReturnTail eta y M) * carryValveReturnTail eta z N := by
    linear_combination h
  rw [he]
  exact (norm_add_le _ _).trans (by
    have hb := norm_add_le
      (conj (carryValveReturnPrefix eta y M) * carryValveReturnTail eta z N)
      (conj (carryValveReturnTail eta y M) * carryValveReturnPrefix eta z N)
    simpa only [norm_mul, Complex.norm_conj] using add_le_add hb
      (le_refl ‖conj (carryValveReturnTail eta y M) * carryValveReturnTail eta z N‖))

/-- Only the complete cell series is used for these limits. -/
theorem carryValveReturn_prefix_tendsto_of_hasSum (eta : ℝ) (y : MaterialCarrier)
    (h : HasSum (carryValveCell eta y) (carryMaterialProjectiveEncode eta y).globalReturn) :
    Tendsto (carryValveReturnPrefix eta y) atTop
      (nhds (carryMaterialProjectiveEncode eta y).globalReturn) := h.tendsto_sum_nat

theorem carryValveReturn_prefix_tendsto (eta : ℝ) (heta : eta ≠ 0)
    (y : completedBoundaryTransportedClock.domain) :
    Tendsto (carryValveReturnPrefix eta y.val) atTop
      (nhds (carryMaterialProjectiveEncode eta y.val).globalReturn) :=
  carryValveReturn_prefix_tendsto_of_hasSum eta y.val (carryValveReturn_graph eta heta y)

theorem carryValveReturn_clock_prefix_tendsto (eta : ℝ) (heta : eta ≠ 0)
    (y : completedBoundaryTransportedClock.domain) :
    Tendsto (carryValveReturnPrefix eta (completedBoundaryTransportedClock y)) atTop
      (nhds (carryMaterialProjectiveEncode eta (completedBoundaryTransportedClock y)).globalReturn) :=
  carryValveReturn_prefix_tendsto_of_hasSum eta _ (carryValveReturn_clock_graph eta heta y)

theorem carryValveReturn_tail_tendsto_of_hasSum (eta : ℝ) (y : MaterialCarrier)
    (h : HasSum (carryValveCell eta y) (carryMaterialProjectiveEncode eta y).globalReturn) :
    Tendsto (carryValveReturnTail eta y) atTop (nhds 0) := by
  change Tendsto (fun M => (carryMaterialProjectiveEncode eta y).globalReturn -
    carryValveReturnPrefix eta y M) atTop (nhds 0)
  simpa only [sub_self] using
    ((tendsto_const_nhds (x := (carryMaterialProjectiveEncode eta y).globalReturn)).sub
      (carryValveReturn_prefix_tendsto_of_hasSum eta y h))

/-- Two genuinely independent cutoffs, not a diagonal choice M=N. -/
theorem carryValveReturn_product_tendsto_of_hasSum (eta : ℝ) (y z : MaterialCarrier)
    (hy : HasSum (carryValveCell eta y) (carryMaterialProjectiveEncode eta y).globalReturn)
    (hz : HasSum (carryValveCell eta z) (carryMaterialProjectiveEncode eta z).globalReturn) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta y p.1) * carryValveReturnPrefix eta z p.2)
      (atTop ×ˢ atTop)
      (nhds (conj (carryMaterialProjectiveEncode eta y).globalReturn *
        (carryMaterialProjectiveEncode eta z).globalReturn)) := by
  exact ((Complex.continuous_conj.tendsto _).comp
    ((carryValveReturn_prefix_tendsto_of_hasSum eta y hy).comp tendsto_fst)).mul
      ((carryValveReturn_prefix_tendsto_of_hasSum eta z hz).comp tendsto_snd)

theorem carryValveReturn_source_product_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) p.1) *
        carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState u) p.2)
      (atTop ×ˢ atTop) (nhds (conj (carryValveBeta t) * carryValveBeta u)) :=
  carryValveReturn_product_tendsto_of_hasSum eta _ _
    (carryValveReturn_source eta heta t) (carryValveReturn_source eta heta u)

theorem carryValveReturn_mixed_product_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) p.1) *
        carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource u)) p.2)
      (atTop ×ˢ atTop) (nhds (conj (carryValveBeta t) * carryValveKappa u)) :=
  carryValveReturn_product_tendsto_of_hasSum eta _ _
    (carryValveReturn_source eta heta t) (carryValveReturn_clock_source eta heta u)

theorem carryValveReturn_clock_ordinary_product_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource t)) p.1) *
        carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState u) p.2)
      (atTop ×ˢ atTop) (nhds (conj (carryValveKappa t) * carryValveBeta u)) :=
  carryValveReturn_product_tendsto_of_hasSum eta _ _
    (carryValveReturn_clock_source eta heta t) (carryValveReturn_source eta heta u)

theorem carryValveReturn_clock_product_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      conj (carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource t)) p.1) *
        carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource u)) p.2)
      (atTop ×ˢ atTop) (nhds (conj (carryValveKappa t) * carryValveKappa u)) :=
  carryValveReturn_product_tendsto_of_hasSum eta _ _
    (carryValveReturn_clock_source eta heta t) (carryValveReturn_clock_source eta heta u)

theorem carryValveReturn_error_tendsto_of_hasSum (eta : ℝ) (y z : MaterialCarrier)
    (hy : HasSum (carryValveCell eta y) (carryMaterialProjectiveEncode eta y).globalReturn)
    (hz : HasSum (carryValveCell eta z) (carryMaterialProjectiveEncode eta z).globalReturn) :
    Tendsto (fun p : ℕ × ℕ =>
      ‖conj (carryMaterialProjectiveEncode eta y).globalReturn *
        (carryMaterialProjectiveEncode eta z).globalReturn -
        conj (carryValveReturnPrefix eta y p.1) * carryValveReturnPrefix eta z p.2‖)
      (atTop ×ˢ atTop) (nhds 0) := by
  simpa only [sub_self, norm_zero] using
    ((tendsto_const_nhds (x := conj (carryMaterialProjectiveEncode eta y).globalReturn *
      (carryMaterialProjectiveEncode eta z).globalReturn)).sub
        (carryValveReturn_product_tendsto_of_hasSum eta y z hy hz)).norm

end
end GeometryOfNumbers.Analysis
