import GeometryOfNumbers.Analysis.CarryMaterialProjectiveGlobalReturn

/-! # The complete bilinear return/clock/dressing Green expression

All infinite sums are whole-cell sums, ordinary or clocked. The hidden Green
complement is retained in the comparison with the original physical pair.
No factor (u-t), time, response or normalization is divided out.
-/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def carryValveSummedSignal (eta t : ℝ) : ℂ :=
  1 + ∑' k, carryValveCell eta (baseTwoCompletedBoundaryHilbertState t) k

def carryValveSummedClock (eta t : ℝ) : ℂ :=
  ∑' k, carryValveCell eta (completedBoundaryTransportedClock (carryValveSource t)) k

theorem carryValveSummedSignal_eq (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveSummedSignal eta t = 1 + carryValveBeta t := by
  rw [carryValveSummedSignal, ← carryValveBeta_eq_tsum eta heta]

theorem carryValveSummedClock_eq (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveSummedClock eta t = carryValveKappa t :=
  (carryValveKappa_eq_tsum eta heta t).symm

def carryValveValueReadout (eta t : ℝ) : ℂ :=
  baseTwoCanonicalDressingScalar t * carryValveSummedSignal eta t

def carryValveCompanionReadout (eta t : ℝ) : ℂ :=
  Complex.I * baseTwoCanonicalDressingScalar t * carryValveSummedClock eta t -
    deriv baseTwoCanonicalDressingScalar t * carryValveSummedSignal eta t

theorem carryValveValueReadout_eq (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveValueReadout eta t = baseTwoCanonicalResponse t := by
  rw [carryValveValueReadout, carryValveSummedSignal_eq eta heta,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]
  congr 1
  simpa only [carryValveBeta, criticalMaterialSample_one] using
    baseTwoCompletedBoundaryValue_add_seed_eq_signal t

theorem carryValveCompanionReadout_eq (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryValveCompanionReadout eta t =
      baseTwoCompletedBoundaryHilbertReadout (carryMaterialCompanionValuePair t).1 := by
  rw [carryValveCompanionReadout, carryValveSummedSignal_eq eta heta, carryValveSummedClock_eq eta heta]
  change _ = baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t (carryValveSource t))
  rw [carryMaterialDressedCompanion_readout, baseTwoCompletedBoundaryHilbertReadout_apply]
  simp only [carryValveSource, carryMaterial_source_seed]
  rfl

def carryValveScalarPair (eta t : ℝ) : ℂ × ℂ :=
  (carryValveCompanionReadout eta t, carryValveValueReadout eta t)

theorem carryValvePair_readout (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    carryMaterialPairReadout (carryMaterialCompanionValuePair t) =
      (carryValveCompanionReadout eta t, 2 * carryValveValueReadout eta t) := by
  apply Prod.ext
  · exact (carryValveCompanionReadout_eq eta heta t).symm
  · rw [carryMaterialCompanionValuePair_readout, carryValveValueReadout_eq eta heta]

/-- This is the full two-argument Green expression, including the derivative
of the same dressing and both ordered return/clock crossings. -/
def carryValveReturnGreen (eta t u : ℝ) : ℂ :=
  Complex.I * conj (baseTwoCanonicalDressingScalar t) * baseTwoCanonicalDressingScalar u *
    (conj (carryValveSummedSignal eta t) * carryValveSummedClock eta u +
     conj (carryValveSummedClock eta t) * carryValveSummedSignal eta u) +
  (conj (deriv baseTwoCanonicalDressingScalar t) * baseTwoCanonicalDressingScalar u -
    conj (baseTwoCanonicalDressingScalar t) * deriv baseTwoCanonicalDressingScalar u) *
      conj (carryValveSummedSignal eta t) * carryValveSummedSignal eta u

theorem carryValveReturnGreen_eq (eta t u : ℝ) :
    carryValveReturnGreen eta t u =
      conj (carryValveValueReadout eta t) * carryValveCompanionReadout eta u -
        conj (carryValveCompanionReadout eta t) * carryValveValueReadout eta u := by
  simp only [carryValveReturnGreen, carryValveValueReadout, carryValveCompanionReadout,
    map_mul, map_sub, Complex.conj_I]
  ring

/-- Original physical Green minus its readout-hidden Green, with the literal
factor 1/2 and the twice-value convention already present in the pair API. -/
theorem carryValveReturnGreen_physical_ledger (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialCompanionValuePair t) (carryMaterialCompanionValuePair u) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialCompanionValuePair t))
        (carryMaterialPairComplement (carryMaterialCompanionValuePair u)) =
      carryValveReturnGreen eta t u := by
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialCompanionValuePair t) (carryMaterialCompanionValuePair u)
  rw [carryValvePair_readout eta heta t, carryValvePair_readout eta heta u] at h
  rw [carryValveReturnGreen_eq]
  simp only [carryMaterialPairGreen, RCLike.inner_apply, map_mul, map_ofNat] at h ⊢
  linear_combination h

def carryValvePrefixValue (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  baseTwoCanonicalDressingScalar t *
    (1 + carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) M)

def carryValvePrefixCompanion (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  Complex.I * baseTwoCanonicalDressingScalar t *
      carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource t)) M -
    deriv baseTwoCanonicalDressingScalar t *
      (1 + carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) M)

def carryValveValueTail (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  baseTwoCanonicalDressingScalar t *
    carryValveReturnTail eta (baseTwoCompletedBoundaryHilbertState t) M

def carryValveCompanionTail (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  Complex.I * baseTwoCanonicalDressingScalar t *
      carryValveReturnTail eta (completedBoundaryTransportedClock (carryValveSource t)) M -
    deriv baseTwoCanonicalDressingScalar t *
      carryValveReturnTail eta (baseTwoCompletedBoundaryHilbertState t) M

def carryValvePrefixPair (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ × ℂ :=
  (carryValvePrefixCompanion eta M t, carryValvePrefixValue eta M t)

def carryValveTailPair (eta : ℝ) (M : ℕ) (t : ℝ) : ℂ × ℂ :=
  (carryValveCompanionTail eta M t, carryValveValueTail eta M t)

theorem carryValvePair_prefix_tail (eta : ℝ) (heta : eta ≠ 0) (M : ℕ) (t : ℝ) :
    carryValveScalarPair eta t = carryValvePrefixPair eta M t + carryValveTailPair eta M t := by
  simp only [carryValveScalarPair, carryValvePrefixPair, carryValveTailPair,
    carryValvePrefixValue, carryValvePrefixCompanion, carryValveValueTail,
    carryValveCompanionTail, carryValveValueReadout, carryValveCompanionReadout,
    carryValveSummedSignal_eq eta heta, carryValveSummedClock_eq eta heta,
    carryValveReturnTail, Prod.mk_add_mk]
  apply Prod.ext <;> dsimp only
  · change _ = Complex.I * baseTwoCanonicalDressingScalar t * _ -
      deriv baseTwoCanonicalDressingScalar t * (1 + _) +
      (Complex.I * baseTwoCanonicalDressingScalar t * (carryValveKappa t - _) -
        deriv baseTwoCanonicalDressingScalar t * (carryValveBeta t - _))
    ring
  · change baseTwoCanonicalDressingScalar t * (1 + carryValveBeta t) =
      baseTwoCanonicalDressingScalar t * (1 + _) +
        baseTwoCanonicalDressingScalar t * (carryValveBeta t - _)
    ring

/-- All four prefix/tail Green terms with M,N independent. -/
theorem carryValveReturnGreen_tail_ledger (eta : ℝ) (heta : eta ≠ 0) (M N : ℕ) (t u : ℝ) :
    carryValveReturnGreen eta t u =
      carryMaterialPairGreen (carryValvePrefixPair eta M t) (carryValvePrefixPair eta N u) +
      carryMaterialPairGreen (carryValvePrefixPair eta M t) (carryValveTailPair eta N u) +
      carryMaterialPairGreen (carryValveTailPair eta M t) (carryValvePrefixPair eta N u) +
      carryMaterialPairGreen (carryValveTailPair eta M t) (carryValveTailPair eta N u) := by
  have he : carryValveReturnGreen eta t u =
      carryMaterialPairGreen (carryValveScalarPair eta t) (carryValveScalarPair eta u) := by
    rw [carryValveReturnGreen_eq]
    simp only [carryMaterialPairGreen, carryValveScalarPair, RCLike.inner_apply]
    ring
  rw [he, carryValvePair_prefix_tail eta heta M t, carryValvePair_prefix_tail eta heta N u]
  simp only [carryMaterialPairGreen, Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  ring

theorem carryValvePrefixValue_tendsto (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    Tendsto (fun M => carryValvePrefixValue eta M t) atTop (nhds (carryValveValueReadout eta t)) := by
  rw [carryValveValueReadout, carryValveSummedSignal_eq eta heta]
  exact tendsto_const_nhds.mul
    (tendsto_const_nhds.add (carryValveReturn_prefix_tendsto eta heta (carryValveSource t)))

theorem carryValvePrefixCompanion_tendsto (eta : ℝ) (heta : eta ≠ 0) (t : ℝ) :
    Tendsto (fun M => carryValvePrefixCompanion eta M t) atTop
      (nhds (carryValveCompanionReadout eta t)) := by
  rw [carryValveCompanionReadout, carryValveSummedSignal_eq eta heta, carryValveSummedClock_eq eta heta]
  exact (tendsto_const_nhds.mul (carryValveReturn_clock_prefix_tendsto eta heta (carryValveSource t))).sub
    (tendsto_const_nhds.mul
      (tendsto_const_nhds.add (carryValveReturn_prefix_tendsto eta heta (carryValveSource t))))

/-- Whole-cell readout Green converges in both independently truncated inputs.
No separate infinite Green/trace channel is used in this argument. -/
theorem carryValvePrefixGreen_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ =>
      carryMaterialPairGreen (carryValvePrefixPair eta p.1 t) (carryValvePrefixPair eta p.2 u))
      (atTop ×ˢ atTop) (nhds (carryValveReturnGreen eta t u)) := by
  rw [carryValveReturnGreen_eq]
  have hf : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop := tendsto_snd
  have hv := (carryValvePrefixValue_tendsto eta heta t).comp hf
  have hw := (carryValvePrefixValue_tendsto eta heta u).comp hs
  have hc := (carryValvePrefixCompanion_tendsto eta heta t).comp hf
  have hd := (carryValvePrefixCompanion_tendsto eta heta u).comp hs
  have he := (((Complex.continuous_conj.tendsto _).comp hv).mul hd).sub
    (((Complex.continuous_conj.tendsto _).comp hc).mul hw)
  simpa only [carryMaterialPairGreen, carryValvePrefixPair, RCLike.inner_apply, mul_comm,
    Function.comp_def] using he

/-- The already fixed source-scale projective reduction, including its signed
companion cross. This is a balance expression, not a positive kernel. -/
def carryValveReducedReturnBalance (eta t u : ℝ) : ℂ :=
  ((carryMaterialResponseScale ^ 2 * t * u : ℝ) : ℂ) * carryValveReturnGreen eta t u -
    (((carryMaterialResponseScale * (u-t) : ℝ) : ℂ) / 2) *
      conj (carryValveCompanionReadout eta t) * carryValveCompanionReadout eta u

theorem carryValveReducedReturnBalance_physical (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
        (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      carryValveReducedReturnBalance eta t u := by
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)
  simp only [carryMaterialReducedCompanionPair, carryMaterialPairReduction_readout] at h
  rw [carryValvePair_readout eta heta t, carryValvePair_readout eta heta u] at h
  rw [carryValveReducedReturnBalance, carryValveReturnGreen_eq]
  simp only [carryMaterialReducedCompanionPair, carryMaterialPairGreen, RCLike.inner_apply, map_sub, map_mul,
    Complex.conj_ofReal, map_ofNat] at h ⊢
  push_cast at h ⊢
  linear_combination h

/-- Finite whole-cell approximation to the SAME reduced balance. No reduced
response is recomputed from a truncated source or its own normalization. -/
def carryValvePrefixReducedBalance (eta : ℝ) (M N : ℕ) (t u : ℝ) : ℂ :=
  ((carryMaterialResponseScale ^ 2 * t * u : ℝ) : ℂ) *
    carryMaterialPairGreen (carryValvePrefixPair eta M t) (carryValvePrefixPair eta N u) -
  (((carryMaterialResponseScale * (u-t) : ℝ) : ℂ) / 2) *
    conj (carryValvePrefixCompanion eta M t) * carryValvePrefixCompanion eta N u

theorem carryValvePrefixReducedBalance_tendsto (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    Tendsto (fun p : ℕ × ℕ => carryValvePrefixReducedBalance eta p.1 p.2 t u)
      (atTop ×ˢ atTop) (nhds (carryValveReducedReturnBalance eta t u)) := by
  have hf : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop := tendsto_snd
  have ht := (carryValvePrefixCompanion_tendsto eta heta t).comp hf
  have hu := (carryValvePrefixCompanion_tendsto eta heta u).comp hs
  exact (tendsto_const_nhds.mul (carryValvePrefixGreen_tendsto eta heta t u)).sub
    ((tendsto_const_nhds.mul ((Complex.continuous_conj.tendsto _).comp ht)).mul hu)

end
end GeometryOfNumbers.Analysis
