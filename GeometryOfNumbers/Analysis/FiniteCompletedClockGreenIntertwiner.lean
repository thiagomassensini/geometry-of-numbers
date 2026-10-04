import GeometryOfNumbers.Analysis.FiniteCompletedBoundaryClock
import GeometryOfNumbers.Analysis.CompletedClockCandidateObstructions
import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator

/-! Finite geometric nodal reconstruction into the existing material/Parseval
clock. Its critical energy is tested before any infinite extension. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProduct lp ENNReal Topology
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeMaterialClock FiniteClockJets GreenStateMaterialLog GreenParsevalMaterialLog
open GreenFrame.Concrete

/-- Even retaining only the ordinary gradient with its standard ℓ² metric
cannot intertwine this material clock with a symmetric target. -/
theorem ordinaryGradient_isometric_intertwiner_impossible
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (J : MaterialEdgeL2 →ₗᵢ[ℂ] K) (A : K →ₗ.[ℂ] K)
    (hA : A.IsFormalAdjoint A)
    (hdom : ∀ x : completedBoundaryTransportedClock.domain, J x.val.snd.fst ∈ A.domain) :
    ¬ (∀ x : completedBoundaryTransportedClock.domain,
      A ⟨J x.val.snd.fst, hdom x⟩ = J (completedBoundaryTransportedClock x).snd.fst) := by
  intro hcomm
  let x : completedBoundaryTransportedClock.domain :=
    ⟨completedBoundaryMaterialDeltaOne, completedBoundaryMaterialDeltaOne_mem_domain⟩
  let y : completedBoundaryTransportedClock.domain :=
    ⟨completedBoundaryMaterialDeltaTwo, completedBoundaryMaterialDeltaTwo_mem_domain⟩
  have h := hA ⟨J x.val.snd.fst, hdom x⟩ ⟨J y.val.snd.fst, hdom y⟩
  rw [hcomm x, hcomm y] at h
  dsimp [x, y] at h
  rw [completedBoundaryTransportedClock_deltaOne, completedBoundaryTransportedClock_deltaTwo] at h
  simp only [WithLp.zero_snd, WithLp.zero_fst, map_zero, inner_zero_left,
    WithLp.smul_snd, WithLp.smul_fst, map_smul] at h
  rw [inner_smul_right (𝕜 := ℂ) _ _ (Real.log 2 : ℂ), J.inner_map_map] at h
  have hi : inner ℂ completedBoundaryMaterialDeltaOne.snd.fst
      completedBoundaryMaterialDeltaTwo.snd.fst = -1 := by
    simp [completedBoundaryMaterialDeltaOne, completedBoundaryMaterialDeltaTwo,
      inner_neg_left, lp.inner_single_left, RCLike.inner_apply]
  rw [hi] at h
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))))
    (by simpa using h.symm)

/-- Zero-extension at the actual material addresses j+1, including its clock domain. -/
def finiteMaterialGreenDomain (M : ℕ) :
    FiniteRealSpectralHilbert M →ₗ[ℂ] greenStateMaterialLogGenerator.domain where
  toFun x := ∑ j : Fin M, x j •
    (⟨greenMaterialBasisVector (natEquivPNat j.val),
      greenMaterialBasisVector_mem_domain _⟩ : greenStateMaterialLogGenerator.domain)
  map_add' x y := by
    apply Subtype.ext
    simp [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    apply Subtype.ext
    simp [PiLp.smul_apply, smul_smul, Finset.smul_sum]

def finiteMaterialGreenEmbedding (M : ℕ) : FiniteRealSpectralHilbert M →ₗ[ℂ] State :=
  greenStateMaterialLogGenerator.domain.subtype.comp (finiteMaterialGreenDomain M)

theorem finiteMaterialGreenEmbedding_sum (M : ℕ) (x : FiniteRealSpectralHilbert M) :
    finiteMaterialGreenEmbedding M x =
      ∑ j : Fin M, x j • greenMaterialBasisVector (natEquivPNat j.val) := by
  simp [finiteMaterialGreenEmbedding, finiteMaterialGreenDomain]

theorem finiteMaterialGreenEmbedding_apply_index (M : ℕ)
    (x : FiniteRealSpectralHilbert M) (j : Fin M) :
    finiteMaterialGreenEmbedding M x (natEquivPNat j.val) = x j := by
  classical
  rw [finiteMaterialGreenEmbedding_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    greenMaterialBasisVector, lp.single_apply]
  have he (k : Fin M) : natEquivPNat j.val = natEquivPNat k.val ↔ j = k := by
    constructor
    · intro h; exact Fin.ext (natEquivPNat.injective h)
    · rintro rfl; rfl
  simp only [Pi.single_apply]
  simp_rw [he]
  simp

theorem finiteMaterialGreenEmbedding_inner (M : ℕ)
    (x y : FiniteRealSpectralHilbert M) :
    inner ℂ (finiteMaterialGreenEmbedding M x) (finiteMaterialGreenEmbedding M y) =
      inner ℂ x y := by
  classical
  rw [finiteMaterialGreenEmbedding_sum M x]
  rw [sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left]
  simp only [greenMaterialBasisVector, lp.inner_single_left, RCLike.inner_apply,
    map_one]

  rw [finiteMaterialGreenEmbedding_apply_index]
  ring

theorem finiteMaterialGreenEmbedding_norm (M : ℕ)
    (x : FiniteRealSpectralHilbert M) : ‖finiteMaterialGreenEmbedding M x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact congrArg Complex.re (finiteMaterialGreenEmbedding_inner M x x)

theorem finiteMaterialGreenEmbedding_injective (M : ℕ) :
    Function.Injective (finiteMaterialGreenEmbedding M) := by
  intro x y h
  ext j
  exact (finiteMaterialGreenEmbedding_apply_index M x j).symm.trans
    ((congrArg (fun f : State => f (natEquivPNat j.val)) h).trans
      (finiteMaterialGreenEmbedding_apply_index M y j))

theorem finiteMaterialGreenEmbedding_clock (M : ℕ) (x : FiniteRealSpectralHilbert M) :
    greenStateMaterialLogGenerator (finiteMaterialGreenDomain M x) =
      finiteMaterialGreenEmbedding M (finiteMaterialClock M x) := by
  rw [finiteMaterialGreenEmbedding_sum]
  change greenStateMaterialLogGenerator.toFun (∑ j : Fin M, x j •
    (⟨greenMaterialBasisVector (natEquivPNat j.val), _⟩ : greenStateMaterialLogGenerator.domain)) =
    ∑ j : Fin M, (finiteMaterialClock M x) j • greenMaterialBasisVector (natEquivPNat j.val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change x j • greenStateMaterialLogGenerator
    ⟨greenMaterialBasisVector (natEquivPNat j.val), _⟩ = _
  rw [greenStateMaterialLogGenerator_basisVector_log]
  simp only [finiteRealSpectralGenerator_apply, finiteRealSpectralFrequency, natEquivPNat_val,
    smul_smul]
  congr 1
  ring

/-- Retain the graph data and one material-clock step before any readout.
The two slots retain seed, ordinary/clock gradients and their derived returns. -/
def finiteCompletedEnrichedSource (N : ℕ) :
    finiteCompletedBoundaryGraph N →ₗ[ℂ]
      WithLp 2 (finiteCompletedBoundaryGraph N × finiteCompletedBoundaryGraph N) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((LinearMap.id : Module.End ℂ (finiteCompletedBoundaryGraph N)).prod
      (finiteCompletedBoundaryClock N))

theorem finiteCompletedEnrichedSource_fst (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    (finiteCompletedEnrichedSource N y).fst = y := rfl

theorem finiteCompletedEnrichedSource_snd (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    (finiteCompletedEnrichedSource N y).snd = finiteCompletedBoundaryClock N y := rfl

theorem finiteCompletedEnrichedSource_injective (N : ℕ) :
    Function.Injective (finiteCompletedEnrichedSource N) := by
  intro x y h
  exact congrArg WithLp.fst h

/-- The enriched ordinary component is the existing material edge prefix. -/
theorem finiteCompletedEnrichedSource_ordinary_orbit (N : ℕ) (t : ℝ) (j : Fin (4*N)) :
    ((finiteCompletedEnrichedSource N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))).fst :
        FiniteCompletedBoundaryCarrier N).snd.fst j = criticalMaterialGradient t j.val :=
  finiteSeedGradientOrbit_historical_gradient (4*N) t j

/-- Its one-step component is the already proved triangular clock coordinate,
not a newly assigned vertical frequency. -/
theorem finiteCompletedEnrichedSource_clockGradient_orbit (N : ℕ) (t : ℝ)
    (j : Fin (4*N)) :
    ((finiteCompletedEnrichedSource N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))).snd :
        FiniteCompletedBoundaryCarrier N).snd.fst j =
      baseTwoCompletedBoundaryHilbertClockCoordinate (baseTwoCompletedBoundaryHilbertState t) j.val := by
  change (finiteSeedGradientClock (4*N) (finiteSeedGradientEncode (4*N)
    (finiteMaterialOrbit (4*N+1) t (historicalInitialState (4*N+1))))).snd j = _
  rw [finiteSeedGradientClock_intertwining, finiteSeedGradientEncode_gradient,
    baseTwoCompletedBoundaryHilbertClockCoordinate_eq]
  simp only [finiteRealSpectralGenerator_apply, finiteRealSpectralFrequency,
    Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]
  rw [← criticalMaterialSample_eq_finiteMaterialOrbit t j.succ,
    ← criticalMaterialSample_eq_finiteMaterialOrbit t j.castSucc]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc, show (1+1:ℕ)=2 by rfl]

/-- Reconstruction uses finite samples only: material edge j is not a depth. -/
def finiteCompletedGraphDecode (N : ℕ) :
    finiteCompletedBoundaryGraph N →ₗ[ℂ] FiniteRealSpectralHilbert (4*N+1) :=
  (finiteSeedGradientDecode (4*N)).comp
    ((finiteCompletedBoundaryForget N).comp (finiteCompletedBoundaryGraph N).subtype)

theorem finiteCompletedGraphDecode_injective (N : ℕ) :
    Function.Injective (finiteCompletedGraphDecode N) := by
  intro x y h
  have hg := congrArg (finiteSeedGradientEncode (4*N)) h
  change finiteSeedGradientEncode (4*N) (finiteSeedGradientDecode (4*N)
    (finiteCompletedBoundaryForget N x)) =
    finiteSeedGradientEncode (4*N) (finiteSeedGradientDecode (4*N)
    (finiteCompletedBoundaryForget N y)) at hg
  rw [finiteSeedGradientEncode_decode, finiteSeedGradientEncode_decode] at hg
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  apply Subtype.ext
  have he : a = b := by
    simpa only [← ha, ← hb, finiteCompletedBoundaryForget_embed] using hg
  exact ha.symm.trans ((congrArg (finiteCompletedBoundaryEmbed N) he).trans hb)

theorem finiteCompletedGraphDecode_clock (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    finiteCompletedGraphDecode N (finiteCompletedBoundaryClock N y) =
      finiteMaterialClock (4*N+1) (finiteCompletedGraphDecode N y) := by
  change finiteSeedGradientDecode (4*N) (finiteSeedGradientClock (4*N)
    (finiteCompletedBoundaryForget N y)) = _
  simp only [finiteSeedGradientClock, LinearMap.comp_apply, finiteSeedGradientDecode_encode]
  rfl

/-- A genuine finite map to the already constructed Parseval Hilbert carrier.
It factors through nodal reconstruction; its infinite norm is not presumed. -/
def finiteCompletedGreenIntertwiner (N : ℕ) :
    finiteCompletedBoundaryGraph N →ₗ[ℂ] ConcreteAnalysisSpace :=
  greenParsevalAnalysis.toLinearMap.comp
    ((finiteMaterialGreenEmbedding (4*N+1)).comp (finiteCompletedGraphDecode N))

theorem finiteCompletedGreenIntertwiner_injective (N : ℕ) :
    Function.Injective (finiteCompletedGreenIntertwiner N) :=
  greenParsevalAnalysis_isometry.injective.comp
    ((finiteMaterialGreenEmbedding_injective _).comp (finiteCompletedGraphDecode_injective N))

theorem finiteCompletedGreenIntertwiner_mem_domain (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    finiteCompletedGreenIntertwiner N y ∈ greenParsevalMaterialLogOperator.domain := by
  apply (greenParsevalMaterialLogOperator_P_mem_domain_iff _).mpr
  exact (finiteMaterialGreenDomain _ (finiteCompletedGraphDecode N y)).property

theorem finiteCompletedGreenIntertwiner_clock (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    greenParsevalMaterialLogOperator
      ⟨finiteCompletedGreenIntertwiner N y, finiteCompletedGreenIntertwiner_mem_domain N y⟩ =
      finiteCompletedGreenIntertwiner N (finiteCompletedBoundaryClock N y) := by
  change greenParsevalMaterialLogOperator
    ⟨greenParsevalAnalysis (finiteMaterialGreenEmbedding _ (finiteCompletedGraphDecode N y)), _⟩ = _
  rw [greenParsevalMaterialLogOperator_intertwining]
  change greenParsevalAnalysis (greenStateMaterialLogGenerator
    (finiteMaterialGreenDomain _ (finiteCompletedGraphDecode N y))) = _
  rw [finiteMaterialGreenEmbedding_clock]
  rw [← finiteCompletedGraphDecode_clock]
  rfl

theorem finiteCompletedGreenIntertwiner_norm (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    ‖finiteCompletedGreenIntertwiner N y‖ = ‖finiteCompletedGraphDecode N y‖ := by
  change ‖greenParsevalAnalysis (finiteMaterialGreenEmbedding _ _)‖ = _
  rw [greenParsevalAnalysis_isometry.norm_map_of_map_zero (map_zero _),
    finiteMaterialGreenEmbedding_norm]

/-- The finite readout graph carries the same raw nodal orbit under Decode. -/
theorem finiteCompletedGraphDecode_orbit (N : ℕ) (t : ℝ)
    (x : FiniteRealSpectralHilbert (4*N+1)) :
    finiteCompletedGraphDecode N (finiteCompletedBoundaryOrbit N t x) =
      finiteMaterialOrbit (4*N+1) t x := by
  change finiteSeedGradientDecode (4*N)
    (finiteSeedGradientEncode (4*N) (finiteMaterialOrbit (4*N+1) t x)) = _
  exact finiteSeedGradientDecode_encode _ _

/-- Exact metric transported from the existing symmetric ambient clock. -/
theorem finiteCompletedGreenIntertwiner_pairing_symmetric (N : ℕ)
    (x y : finiteCompletedBoundaryGraph N) :
    inner ℂ (finiteCompletedGreenIntertwiner N (finiteCompletedBoundaryClock N x))
      (finiteCompletedGreenIntertwiner N y) =
    inner ℂ (finiteCompletedGreenIntertwiner N x)
      (finiteCompletedGreenIntertwiner N (finiteCompletedBoundaryClock N y)) := by
  have hA := greenParsevalMaterialLogOperator_isSelfAdjoint
  have he := LinearPMap.isSelfAdjoint_def.mp hA
  have hf := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    (T := greenParsevalMaterialLogOperator)
  rw [he] at hf
  have h := hf ⟨finiteCompletedGreenIntertwiner N x,
    finiteCompletedGreenIntertwiner_mem_domain N x⟩
    ⟨finiteCompletedGreenIntertwiner N y, finiteCompletedGreenIntertwiner_mem_domain N y⟩
  simpa only [finiteCompletedGreenIntertwiner_clock] using h

/-- No renormalization: the critical nodal Parseval energy is a harmonic prefix. -/
theorem finiteCompletedGreenIntertwiner_critical_energy (N : ℕ) (t : ℝ) :
    ‖finiteCompletedGreenIntertwiner N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))‖ ^ 2 =
      ∑ j ∈ Finset.range (4*N+1), ((j+1 : ℕ) : ℝ)⁻¹ := by
  rw [finiteCompletedGreenIntertwiner_norm, finiteCompletedGraphDecode_orbit,
    EuclideanSpace.norm_sq_eq]
  simp_rw [← criticalMaterialSample_eq_finiteMaterialOrbit,
    criticalMaterialSample_norm_sq t _ (Nat.succ_pos _)]
  exact Fin.sum_univ_eq_sum_range (fun j => ((j+1 : ℕ) : ℝ)⁻¹) _

/-- The synchronized geometric cutoffs do not remove harmonic divergence. -/
theorem finiteCompletedGreenIntertwiner_critical_energy_tendsto (t : ℝ) :
    Filter.Tendsto (fun N => ‖finiteCompletedGreenIntertwiner N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))‖ ^ 2)
      Filter.atTop Filter.atTop := by
  simp_rw [finiteCompletedGreenIntertwiner_critical_energy]
  have hN : Filter.Tendsto (fun N : ℕ => 4*N+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by change N ≤ 4*N+1; omega) (Filter.tendsto_id :
      Filter.Tendsto (fun N : ℕ => N) Filter.atTop Filter.atTop)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using
    Real.tendsto_sum_range_one_div_nat_succ_atTop.comp hN

/-- This specific lossless nodal Green candidate has no ambient Hilbert limit.
It does not exclude a different enriched geometric energy. -/
theorem finiteCompletedGreenIntertwiner_critical_no_limit (t : ℝ) :
    ¬ ∃ z : ConcreteAnalysisSpace,
      Filter.Tendsto (fun N => finiteCompletedGreenIntertwiner N
        (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1))))
        Filter.atTop (nhds z) := by
  rintro ⟨z, hz⟩
  have hn := (continuous_norm.pow 2).tendsto z |>.comp hz
  exact not_tendsto_nhds_of_tendsto_atTop
    (finiteCompletedGreenIntertwiner_critical_energy_tendsto t) (‖z‖^2)
    (by simpa only [Function.comp_def, Pi.pow_apply] using hn)

/-- The enriched source is sent losslessly to two existing Green carriers:
ordinary nodal reconstruction and its independently derived clock step. -/
def finiteCompletedEnrichedGreenAnalysis (N : ℕ) :
    finiteCompletedBoundaryGraph N →ₗ[ℂ]
      WithLp 2 (ConcreteAnalysisSpace × ConcreteAnalysisSpace) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((finiteCompletedGreenIntertwiner N).prod
      ((finiteCompletedGreenIntertwiner N).comp (finiteCompletedBoundaryClock N)))

theorem finiteCompletedEnrichedGreenAnalysis_injective (N : ℕ) :
    Function.Injective (finiteCompletedEnrichedGreenAnalysis N) := by
  intro x y h
  apply finiteCompletedGreenIntertwiner_injective N
  exact congrArg WithLp.fst h

/-- Both ordinary and one-clock-step channels intertwine the same existing
partial Green clock. The second statement is not a fitted clock jet. -/
theorem finiteCompletedEnrichedGreenAnalysis_clock (N : ℕ)
    (y : finiteCompletedBoundaryGraph N) :
    greenParsevalMaterialLogOperator
      ⟨(finiteCompletedEnrichedGreenAnalysis N y).fst,
        finiteCompletedGreenIntertwiner_mem_domain N y⟩ =
      (finiteCompletedEnrichedGreenAnalysis N (finiteCompletedBoundaryClock N y)).fst ∧
    greenParsevalMaterialLogOperator
      ⟨(finiteCompletedEnrichedGreenAnalysis N y).snd,
        finiteCompletedGreenIntertwiner_mem_domain N (finiteCompletedBoundaryClock N y)⟩ =
      (finiteCompletedEnrichedGreenAnalysis N (finiteCompletedBoundaryClock N y)).snd :=
  ⟨finiteCompletedGreenIntertwiner_clock N y,
    finiteCompletedGreenIntertwiner_clock N (finiteCompletedBoundaryClock N y)⟩

/-- Enrichment retains, rather than cancels, the raw nodal clock energy. -/
theorem finiteCompletedEnrichedGreenAnalysis_critical_energy (N : ℕ) (t : ℝ) :
    ‖finiteCompletedEnrichedGreenAnalysis N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))‖ ^ 2 =
      ∑ j ∈ Finset.range (4*N+1),
        (1 + (Real.log ((j+1 : ℕ) : ℝ))^2) * ((j+1 : ℕ) : ℝ)⁻¹ := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖finiteCompletedGreenIntertwiner N _‖ ^ 2 +
    ‖finiteCompletedGreenIntertwiner N (finiteCompletedBoundaryClock N _)‖ ^ 2 = _
  rw [finiteCompletedGreenIntertwiner_critical_energy, finiteCompletedGreenIntertwiner_norm,
    finiteCompletedGraphDecode_clock, finiteCompletedGraphDecode_orbit, EuclideanSpace.norm_sq_eq]
  simp_rw [finiteRealSpectralGenerator_apply, finiteRealSpectralFrequency, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← criticalMaterialSample_eq_finiteMaterialOrbit,
    criticalMaterialSample_norm_sq t _ (Nat.succ_pos _)]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (Real.log ((j+1 : ℕ) : ℝ))^2 * ((j+1 : ℕ) : ℝ)⁻¹), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteCompletedEnrichedGreenAnalysis_critical_energy_tendsto (t : ℝ) :
    Filter.Tendsto (fun N => ‖finiteCompletedEnrichedGreenAnalysis N
      (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1)))‖ ^ 2)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono _ (finiteCompletedGreenIntertwiner_critical_energy_tendsto t)
  intro N
  rw [WithLp.prod_norm_sq_eq_of_L2 (finiteCompletedEnrichedGreenAnalysis N
    (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1))))]
  change ‖finiteCompletedGreenIntertwiner N _‖ ^ 2 ≤
    ‖finiteCompletedGreenIntertwiner N _‖ ^ 2 + _
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem finiteCompletedEnrichedGreenAnalysis_critical_no_limit (t : ℝ) :
    ¬ ∃ z : WithLp 2 (ConcreteAnalysisSpace × ConcreteAnalysisSpace),
      Filter.Tendsto (fun N => finiteCompletedEnrichedGreenAnalysis N
        (finiteCompletedBoundaryOrbit N t (historicalInitialState (4*N+1))))
        Filter.atTop (nhds z) := by
  rintro ⟨z, hz⟩
  have hn := (continuous_norm.pow 2).tendsto z |>.comp hz
  exact not_tendsto_nhds_of_tendsto_atTop
    (finiteCompletedEnrichedGreenAnalysis_critical_energy_tendsto t) (‖z‖^2)
    (by simpa only [Function.comp_def, Pi.pow_apply] using hn)

end GeometryOfNumbers.Analysis.BaseTwoCompletion
