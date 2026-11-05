import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceAtlas
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceNoGo
import NativeCarryC3Crosswalk.EnrichedBoundaryCarrier
import NativeCarrySpectralWeyl.Boundary.GreenRelation
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The canonical nonlocal arithmetic trace

The finite enriched Genuine/`G_pre` bracket produces a mass-normalized
prime-camera profile.  Removing its final carry amplitude is not a bounded
operation on the completed prime-camera Hilbert space: it is multiplication
by `sqrt(p)`.  This file packages that operation canonically, without a
pseudoinverse or a chosen representative.

We first construct the bounded injective damping map

`R(v)(p) = p^(-1/2) v(p)`

and define the arithmetic nonlocal trace as its maximal `LinearPMap` inverse.
Consequently its domain is explicit, the operator is closed, and its graph is
the enriched boundary port retaining both mass and upgraded Green data.

The finite bracket--TFVD--Green intertwining is unconditional.  Globally,
however, the concrete mass state lies in the trace domain exactly on the
half-abscissa.  Hence this construction deliberately does **not** infer domain
membership from a Genuine zero.  That implication is the remaining
arithmetic regularity gate, not part of the trace definition.
-/

open scoped ENNReal InnerProductSpace LinearPMap
open Set LinearPMap

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Completed carrier of mass-normalized prime-camera readouts. -/
abbrev ArithmeticMassCarrier := PrimeGreenCameraHilbert

/-- Enriched boundary port retaining the mass input and Green output. -/
abbrev ArithmeticEnrichedBoundaryPort :=
  ArithmeticMassCarrier × ArithmeticMassCarrier

private theorem primeAmplitudeDampingWeight_nonneg (p : Nat.Primes) :
    0 ≤ primeCarryAmplitudeRatio p :=
  primeCarryAmplitudeRatio_nonneg p

private theorem primeAmplitudeDampingWeight_le_one (p : Nat.Primes) :
    primeCarryAmplitudeRatio p ≤ 1 :=
  (primeCarryAmplitudeRatio_lt_one p p.prop.two_le).le

private theorem primeAmplitudeDampingWeight_ne_zero (p : Nat.Primes) :
    primeCarryAmplitudeRatio p ≠ 0 :=
  primeCarryAmplitudeRatio_ne_zero_prime p

/-- Pointwise damping by one critical carry amplitude. -/
private def arithmeticPrimeDampingValue
    (x : ArithmeticMassCarrier) : ArithmeticMassCarrier :=
  ⟨fun p => primeCarryAmplitudeRatio p * x p, by
    change Memℓp
      (fun p : Nat.Primes => primeCarryAmplitudeRatio p * x p) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hx := (lp.memℓp x).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact Summable.of_nonneg_of_le
      (fun p => by positivity)
      (fun p => by
        rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
          Real.rpow_two, norm_mul, Real.norm_of_nonneg
            (primeAmplitudeDampingWeight_nonneg p)]
        have hq0 := primeAmplitudeDampingWeight_nonneg p
        have hq1 := primeAmplitudeDampingWeight_le_one p
        have hqsq : (primeCarryAmplitudeRatio p) ^ 2 ≤ 1 := by
          nlinarith [sq_nonneg (primeCarryAmplitudeRatio p)]
        rw [mul_pow]
        simpa using
          (mul_le_mul_of_nonneg_right hqsq (sq_nonneg ‖x p‖)))
      hx⟩

@[simp] private theorem arithmeticPrimeDampingValue_apply
    (x : ArithmeticMassCarrier) (p : Nat.Primes) :
    arithmeticPrimeDampingValue x p =
      primeCarryAmplitudeRatio p * x p := rfl

private theorem arithmeticPrimeDampingValue_add
    (x y : ArithmeticMassCarrier) :
    arithmeticPrimeDampingValue (x + y) =
      arithmeticPrimeDampingValue x + arithmeticPrimeDampingValue y := by
  apply lp.ext
  funext p
  simp [mul_add]

private theorem arithmeticPrimeDampingValue_smul
    (c : ℝ) (x : ArithmeticMassCarrier) :
    arithmeticPrimeDampingValue (c • x) =
      c • arithmeticPrimeDampingValue x := by
  apply lp.ext
  funext p
  simp [mul_left_comm]

private theorem arithmeticPrimeDampingValue_norm_sq_le
    (x : ArithmeticMassCarrier) :
    ‖arithmeticPrimeDampingValue x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  calc
    ‖arithmeticPrimeDampingValue x‖ ^ 2 =
        ∑' p : Nat.Primes, ‖arithmeticPrimeDampingValue x p‖ ^ 2 := by
      simpa [Real.rpow_two] using
        (lp.norm_rpow_eq_tsum hp (arithmeticPrimeDampingValue x))
    _ ≤ ∑' p : Nat.Primes, ‖x p‖ ^ 2 :=
      ((lp.memℓp (arithmeticPrimeDampingValue x)).summable hp).tsum_le_tsum
        (fun p => by
          rw [arithmeticPrimeDampingValue_apply, norm_mul,
            Real.norm_of_nonneg (primeAmplitudeDampingWeight_nonneg p)]
          have hq0 := primeAmplitudeDampingWeight_nonneg p
          have hq1 := primeAmplitudeDampingWeight_le_one p
          have hqsq : (primeCarryAmplitudeRatio p) ^ 2 ≤ 1 := by
            nlinarith [sq_nonneg (primeCarryAmplitudeRatio p)]
          simpa [Real.rpow_two, pow_two, mul_assoc, mul_left_comm,
            mul_comm] using
            (mul_le_mul_of_nonneg_right hqsq (sq_nonneg ‖x p‖)))
        ((lp.memℓp x).summable hp)
    _ = ‖x‖ ^ 2 := by
      simpa [Real.rpow_two] using (lp.norm_rpow_eq_tsum hp x).symm

private theorem arithmeticPrimeDampingValue_norm_le
    (x : ArithmeticMassCarrier) :
    ‖arithmeticPrimeDampingValue x‖ ≤ ‖x‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (arithmeticPrimeDampingValue_norm_sq_le x)

/-- Bounded damping by the critical carry amplitude `p^(-1/2)`. -/
def arithmeticPrimeDamping :
    ArithmeticMassCarrier →L[ℝ] ArithmeticMassCarrier :=
  ({
    toFun := arithmeticPrimeDampingValue
    map_add' := arithmeticPrimeDampingValue_add
    map_smul' := arithmeticPrimeDampingValue_smul
  } : ArithmeticMassCarrier →ₗ[ℝ] ArithmeticMassCarrier).mkContinuous
    1 fun x => by
      change ‖arithmeticPrimeDampingValue x‖ ≤ 1 * ‖x‖
      simpa using arithmeticPrimeDampingValue_norm_le x

@[simp] theorem arithmeticPrimeDamping_apply
    (x : ArithmeticMassCarrier) (p : Nat.Primes) :
    arithmeticPrimeDamping x p =
      primeCarryAmplitudeRatio p * x p := rfl

theorem arithmeticPrimeDamping_injective :
    Function.Injective arithmeticPrimeDamping := by
  intro x y hxy
  apply lp.ext
  funext p
  have hp := congrArg (fun z : ArithmeticMassCarrier => z p) hxy
  simp only [arithmeticPrimeDamping_apply] at hp
  exact mul_left_cancel₀ (primeAmplitudeDampingWeight_ne_zero p) hp

/-- The damping is symmetric because its diagonal weights are real. -/
theorem arithmeticPrimeDamping_isSymmetric :
    LinearMap.IsSymmetric arithmeticPrimeDamping.toLinearMap := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro p
  change inner ℝ (primeCarryAmplitudeRatio p * x p) (y p) =
    inner ℝ (x p) (primeCarryAmplitudeRatio p * y p)
  simp
  ring

/-- The injective symmetric damping has dense range. -/
theorem arithmeticPrimeDamping_denseRange :
    Dense (LinearMap.range arithmeticPrimeDamping.toLinearMap :
      Set ArithmeticMassCarrier) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [← (LinearMap.range
      arithmeticPrimeDamping.toLinearMap).orthogonal_orthogonal_eq_closure]
  rw [arithmeticPrimeDamping_isSymmetric.orthogonal_range,
    LinearMap.ker_eq_bot.mpr arithmeticPrimeDamping_injective,
    Submodule.bot_orthogonal_eq_top]

/-- The bounded damping viewed as an everywhere-defined partial operator. -/
def arithmeticPrimeDampingPMap :
    ArithmeticMassCarrier →ₗ.[ℝ] ArithmeticMassCarrier :=
  arithmeticPrimeDamping.toLinearMap.toPMap ⊤

@[simp] theorem arithmeticPrimeDampingPMap_domain :
    arithmeticPrimeDampingPMap.domain = ⊤ := rfl

@[simp] theorem arithmeticPrimeDampingPMap_apply
    (x : arithmeticPrimeDampingPMap.domain) :
    arithmeticPrimeDampingPMap x = arithmeticPrimeDamping x := rfl

theorem arithmeticPrimeDampingPMap_toFun_injective :
    Function.Injective arithmeticPrimeDampingPMap.toFun := by
  intro x y hxy
  apply Subtype.ext
  apply arithmeticPrimeDamping_injective
  exact hxy

theorem arithmeticPrimeDampingPMap_ker_eq_bot :
    arithmeticPrimeDampingPMap.ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot]
  intro x y hxy
  exact arithmeticPrimeDampingPMap_toFun_injective hxy

theorem arithmeticPrimeDampingPMap_range :
    LinearMap.range arithmeticPrimeDampingPMap.toFun =
      LinearMap.range arithmeticPrimeDamping.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, by simp⟩, rfl⟩

/-- The damping range is exactly the mass profiles supporting the canonical
prime-amplitude upgrade. -/
theorem mem_range_arithmeticPrimeDamping_iff
    (mass : ArithmeticMassCarrier) :
    mass ∈ LinearMap.range arithmeticPrimeDamping.toLinearMap ↔
      PrimeAmplitudeUpgradeDomain mass := by
  constructor
  · rintro ⟨amplitude, rfl⟩
    rw [← exists_primeAmplitudeUpgradeGraphPair_iff]
    refine ⟨amplitude, ?_⟩
    intro p
    change amplitude p = (primeCarryAmplitudeRatio p)⁻¹ *
      (primeCarryAmplitudeRatio p * amplitude p)
    field_simp [primeAmplitudeDampingWeight_ne_zero p]
  · intro hdomain
    rw [← exists_primeAmplitudeUpgradeGraphPair_iff] at hdomain
    rcases hdomain with ⟨amplitude, hgraph⟩
    refine ⟨amplitude, ?_⟩
    apply lp.ext
    funext p
    change primeCarryAmplitudeRatio p * amplitude p = mass p
    rw [hgraph p]
    field_simp [primeAmplitudeDampingWeight_ne_zero p]

/-- The canonical nonlocal arithmetic trace: maximal inverse of the bounded
critical-amplitude damping.  It multiplies coordinate `p` by `sqrt(p)` on its
maximal square-summable domain. -/
def arithmeticNonlocalTrace :
    ArithmeticMassCarrier →ₗ.[ℝ] ArithmeticMassCarrier :=
  arithmeticPrimeDampingPMap.inverse

@[simp] theorem mem_arithmeticNonlocalTrace_domain_iff
    (mass : ArithmeticMassCarrier) :
    mass ∈ arithmeticNonlocalTrace.domain ↔
      PrimeAmplitudeUpgradeDomain mass := by
  rw [arithmeticNonlocalTrace, LinearPMap.inverse_domain,
    arithmeticPrimeDampingPMap_range,
    mem_range_arithmeticPrimeDamping_iff]

theorem arithmeticPrimeDampingPMap_isClosed :
    arithmeticPrimeDampingPMap.IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : (arithmeticPrimeDampingPMap.graph : Set
      (ArithmeticMassCarrier × ArithmeticMassCarrier)) =
      {z | arithmeticPrimeDamping z.1 = z.2} := by
    ext z
    simp [LinearPMap.mem_graph_iff, arithmeticPrimeDampingPMap]
  rw [hgraph]
  exact isClosed_eq
    (arithmeticPrimeDamping.continuous.comp continuous_fst) continuous_snd

/-- The arithmetic trace is a genuinely closed (hence closable) unbounded
operator, not merely a formal graph predicate. -/
theorem arithmeticNonlocalTrace_isClosed :
    arithmeticNonlocalTrace.IsClosed := by
  exact
    (LinearPMap.inverse_closed_iff arithmeticPrimeDampingPMap_ker_eq_bot).2
      arithmeticPrimeDampingPMap_isClosed

theorem arithmeticNonlocalTrace_isClosable :
    arithmeticNonlocalTrace.IsClosable :=
  arithmeticNonlocalTrace_isClosed.isClosable

/-- The maximal trace domain is dense in the prime-camera Hilbert carrier. -/
theorem arithmeticNonlocalTrace_denseDomain :
    Dense (arithmeticNonlocalTrace.domain : Set ArithmeticMassCarrier) := by
  rw [arithmeticNonlocalTrace, LinearPMap.inverse_domain,
    arithmeticPrimeDampingPMap_range]
  exact arithmeticPrimeDamping_denseRange

private def arithmeticPrimeDampingDomainElement
    (x : ArithmeticMassCarrier) : arithmeticPrimeDampingPMap.domain :=
  ⟨x, by simp⟩

/-- Canonical domain point obtained by damping an arbitrary amplitude state. -/
def arithmeticPrimeDampingRangeElement
    (x : ArithmeticMassCarrier) : arithmeticNonlocalTrace.domain :=
  ⟨arithmeticPrimeDamping x, by
    rw [arithmeticNonlocalTrace, LinearPMap.inverse_domain,
      arithmeticPrimeDampingPMap_range]
    exact LinearMap.mem_range_self _ x⟩

@[simp] theorem arithmeticNonlocalTrace_apply_dampingRangeElement
    (x : ArithmeticMassCarrier) :
    arithmeticNonlocalTrace (arithmeticPrimeDampingRangeElement x) = x := by
  simpa [arithmeticNonlocalTrace, arithmeticPrimeDampingDomainElement] using
    (LinearPMap.inverse_apply_eq arithmeticPrimeDampingPMap_ker_eq_bot
      (x := arithmeticPrimeDampingDomainElement x)
      (y := arithmeticPrimeDampingRangeElement x) (by rfl))

private def arithmeticNonlocalTraceValue
    (mass : arithmeticNonlocalTrace.domain) : ArithmeticMassCarrier :=
  ⟨fun p => (primeCarryAmplitudeRatio p)⁻¹ *
      (mass : ArithmeticMassCarrier) p, by
    change Memℓp
      (fun p : Nat.Primes => (primeCarryAmplitudeRatio p)⁻¹ *
        (mass : ArithmeticMassCarrier) p) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hdomain : PrimeAmplitudeUpgradeDomain
        (mass : ArithmeticMassCarrier) :=
      (mem_arithmeticNonlocalTrace_domain_iff _).1 mass.2
    exact hdomain.congr fun p => by
      rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
        Real.rpow_two]
      exact (sq_abs _).symm⟩

theorem arithmeticNonlocalTrace_apply_coordinate
    (mass : arithmeticNonlocalTrace.domain) (p : Nat.Primes) :
    arithmeticNonlocalTrace mass p =
      (primeCarryAmplitudeRatio p)⁻¹ *
        (mass : ArithmeticMassCarrier) p := by
  let amplitude := arithmeticNonlocalTraceValue mass
  have hdamping : arithmeticPrimeDamping amplitude = mass := by
    apply lp.ext
    funext q
    change primeCarryAmplitudeRatio q *
        ((primeCarryAmplitudeRatio q)⁻¹ *
          (mass : ArithmeticMassCarrier) q) =
      (mass : ArithmeticMassCarrier) q
    field_simp [primeAmplitudeDampingWeight_ne_zero q]
  have hrange : arithmeticPrimeDampingRangeElement amplitude = mass := by
    apply Subtype.ext
    exact hdamping
  rw [← hrange, arithmeticNonlocalTrace_apply_dampingRangeElement]
  change amplitude p = (primeCarryAmplitudeRatio p)⁻¹ *
    (primeCarryAmplitudeRatio p * amplitude p)
  field_simp [primeAmplitudeDampingWeight_ne_zero p]

/-- The closed trace graph is exactly the previously identified diagonal
prime-amplitude upgrade relation. -/
theorem arithmeticNonlocalTrace_isPrimeAmplitudeUpgradeGraphPair
    (mass : arithmeticNonlocalTrace.domain) :
    IsPrimeAmplitudeUpgradeGraphPair
      (mass : ArithmeticMassCarrier) (arithmeticNonlocalTrace mass) := by
  intro p
  exact arithmeticNonlocalTrace_apply_coordinate mass p

/-- The maximal arithmetic trace is symmetric on its explicit domain. -/
theorem arithmeticNonlocalTrace_isFormalAdjoint :
    arithmeticNonlocalTrace.IsFormalAdjoint arithmeticNonlocalTrace := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro p
  rw [arithmeticNonlocalTrace_apply_coordinate,
    arithmeticNonlocalTrace_apply_coordinate]
  change inner ℝ
      ((primeCarryAmplitudeRatio p)⁻¹ *
        (x : ArithmeticMassCarrier) p)
      ((y : ArithmeticMassCarrier) p) =
    inner ℝ ((x : ArithmeticMassCarrier) p)
      ((primeCarryAmplitudeRatio p)⁻¹ *
        (y : ArithmeticMassCarrier) p)
  simp
  ring

/-- Every adjoint-domain vector is obtained from the bounded damping applied
to its adjoint image. -/
theorem arithmeticPrimeDamping_apply_arithmeticNonlocalTrace_adjoint
    (y : arithmeticNonlocalTrace†.domain) :
    arithmeticPrimeDamping (arithmeticNonlocalTrace† y) =
      (y : ArithmeticMassCarrier) := by
  apply (InnerProductSpace.toDualMap ℝ ArithmeticMassCarrier).injective
  apply ContinuousLinearMap.ext
  intro u
  simp only [InnerProductSpace.toDualMap_apply_apply]
  calc
    ⟪arithmeticPrimeDamping (arithmeticNonlocalTrace† y), u⟫_ℝ =
        ⟪arithmeticNonlocalTrace† y, arithmeticPrimeDamping u⟫_ℝ :=
      arithmeticPrimeDamping_isSymmetric _ _
    _ = ⟪(y : ArithmeticMassCarrier),
          arithmeticNonlocalTrace
            (arithmeticPrimeDampingRangeElement u)⟫_ℝ :=
      arithmeticNonlocalTrace.adjoint_isFormalAdjoint
        arithmeticNonlocalTrace_denseDomain y
          (arithmeticPrimeDampingRangeElement u)
    _ = ⟪(y : ArithmeticMassCarrier), u⟫_ℝ := by
      rw [arithmeticNonlocalTrace_apply_dampingRangeElement]

/-- The adjoint domain contains no vectors beyond the explicit maximal trace
domain. -/
theorem arithmeticNonlocalTrace_adjoint_domain_le :
    arithmeticNonlocalTrace†.domain ≤ arithmeticNonlocalTrace.domain := by
  intro y hy
  rw [arithmeticNonlocalTrace, LinearPMap.inverse_domain,
    arithmeticPrimeDampingPMap_range]
  let y' : arithmeticNonlocalTrace†.domain := ⟨y, hy⟩
  refine ⟨arithmeticNonlocalTrace† y', ?_⟩
  exact arithmeticPrimeDamping_apply_arithmeticNonlocalTrace_adjoint y'

/-- Maximality of the diagonal prime-amplitude trace. -/
theorem arithmeticNonlocalTrace_adjoint_le :
    arithmeticNonlocalTrace† ≤ arithmeticNonlocalTrace := by
  refine ⟨arithmeticNonlocalTrace_adjoint_domain_le, ?_⟩
  intro x y hxy
  let z : ArithmeticMassCarrier := arithmeticNonlocalTrace† x
  have hz : arithmeticPrimeDamping z = (x : ArithmeticMassCarrier) :=
    arithmeticPrimeDamping_apply_arithmeticNonlocalTrace_adjoint x
  have hrange : arithmeticPrimeDampingRangeElement z = y := by
    apply Subtype.ext
    exact hz.trans hxy
  calc
    arithmeticNonlocalTrace† x = z := rfl
    _ = arithmeticNonlocalTrace (arithmeticPrimeDampingRangeElement z) :=
      (arithmeticNonlocalTrace_apply_dampingRangeElement z).symm
    _ = arithmeticNonlocalTrace y := by rw [hrange]

/-- The nonlocal arithmetic trace is self-adjoint, hence stronger than merely
closed or closable. -/
theorem arithmeticNonlocalTrace_isSelfAdjoint :
    IsSelfAdjoint arithmeticNonlocalTrace := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm arithmeticNonlocalTrace_adjoint_le
    (arithmeticNonlocalTrace_isFormalAdjoint.le_adjoint
      arithmeticNonlocalTrace_denseDomain)

/-- Fixed enriched boundary relation selected by the nonlocal arithmetic
trace.  A boundary pair belongs to it precisely when its second coordinate is
the canonical amplitude upgrade of its first. -/
def arithmeticNonlocalBoundaryRelation :
    GreenRelation ℝ ArithmeticMassCarrier :=
  operatorRelation arithmeticNonlocalTrace

/-- The relation is closed because the arithmetic trace is closed. -/
theorem arithmeticNonlocalBoundaryRelation_isClosed :
    IsClosed (arithmeticNonlocalBoundaryRelation :
      Set ArithmeticEnrichedBoundaryPort) := by
  simpa [arithmeticNonlocalBoundaryRelation, operatorRelation,
    LinearPMap.IsClosed] using arithmeticNonlocalTrace_isClosed

/-- The fixed trace graph is maximal Green-isotropic. -/
theorem arithmeticNonlocalBoundaryRelation_isMaximalGreenIsotropic :
    IsMaximalGreenIsotropic arithmeticNonlocalBoundaryRelation := by
  exact operatorRelation_isMaximalGreenIsotropic arithmeticNonlocalTrace
    arithmeticNonlocalTrace_isSelfAdjoint

theorem arithmeticNonlocalBoundaryRelation_isGreenIsotropic :
    IsGreenIsotropic arithmeticNonlocalBoundaryRelation :=
  isMaximalGreenIsotropic_isGreenIsotropic
    arithmeticNonlocalBoundaryRelation_isMaximalGreenIsotropic

/-- `J_arith` as the canonical graph embedding.  It retains both the
mass-normalized endpoint and its nonlocal Green output. -/
def arithmeticNonlocalBoundaryPort :
    arithmeticNonlocalTrace.domain →ₗ[ℝ]
      ArithmeticEnrichedBoundaryPort where
  toFun mass := ((mass : ArithmeticMassCarrier),
    arithmeticNonlocalTrace mass)
  map_add' x y := by
    ext <;> simp [LinearPMap.map_add]
  map_smul' c x := by
    ext <;> simp [LinearPMap.map_smul]

/-- Every value of `J_arith` belongs to the fixed closed boundary relation,
without a zero or half-abscissa hypothesis. -/
theorem arithmeticNonlocalBoundaryPort_mem_relation
    (mass : arithmeticNonlocalTrace.domain) :
    arithmeticNonlocalBoundaryPort mass ∈
      arithmeticNonlocalBoundaryRelation := by
  exact LinearPMap.mem_graph arithmeticNonlocalTrace mass

/-! ## A concrete defect for the fixed relation -/

/-- Natural domain of the boundary defect: the endpoint must lie in the
nonlocal trace domain, while the proposed Green leg is arbitrary. -/
def arithmeticBoundaryDefectDomain :
    Submodule ℝ ArithmeticEnrichedBoundaryPort :=
  arithmeticNonlocalTrace.domain.prod ⊤

/-- Concrete defect characterizing the fixed graph relation:
`D∂(mass, green) = green - J_nonlocal(mass)`. -/
def arithmeticBoundaryDefect :
    ArithmeticEnrichedBoundaryPort →ₗ.[ℝ] ArithmeticMassCarrier where
  domain := arithmeticBoundaryDefectDomain
  toFun :=
    { toFun := fun port =>
        port.1.2 - arithmeticNonlocalTrace
          ⟨port.1.1, port.2.1⟩
      map_add' := by
        intro x y
        change (x.1.2 + y.1.2) -
            arithmeticNonlocalTrace
              (⟨x.1.1, x.2.1⟩ + ⟨y.1.1, y.2.1⟩) =
          (x.1.2 - arithmeticNonlocalTrace ⟨x.1.1, x.2.1⟩) +
            (y.1.2 - arithmeticNonlocalTrace ⟨y.1.1, y.2.1⟩)
        rw [LinearPMap.map_add]
        abel
      map_smul' := by
        intro c x
        change (c • x.1.2) -
            arithmeticNonlocalTrace (c • ⟨x.1.1, x.2.1⟩) =
          c • (x.1.2 - arithmeticNonlocalTrace ⟨x.1.1, x.2.1⟩)
        rw [LinearPMap.map_smul]
        module }

/-- The defect vanishes exactly on the fixed maximal isotropic relation. -/
theorem arithmeticBoundaryDefect_eq_zero_iff_mem_relation
    (port : arithmeticBoundaryDefect.domain) :
    arithmeticBoundaryDefect port = 0 ↔
      (port : ArithmeticEnrichedBoundaryPort) ∈
        arithmeticNonlocalBoundaryRelation := by
  change port.1.2 - arithmeticNonlocalTrace
      ⟨port.1.1, port.2.1⟩ = 0 ↔ _
  rw [sub_eq_zero, arithmeticNonlocalBoundaryRelation, operatorRelation,
    LinearPMap.mem_graph_iff]
  constructor
  · intro h
    exact ⟨⟨port.1.1, port.2.1⟩, rfl, h.symm⟩
  · rintro ⟨mass, hmass, hvalue⟩
    have hsubtype : mass = ⟨port.1.1, port.2.1⟩ := by
      apply Subtype.ext
      exact hmass
    simpa [hsubtype] using hvalue.symm

/-- The graph port as an element of the concrete defect domain. -/
def arithmeticNonlocalBoundaryPortInDefectDomain
    (mass : arithmeticNonlocalTrace.domain) :
    arithmeticBoundaryDefect.domain :=
  ⟨arithmeticNonlocalBoundaryPort mass, ⟨mass.2, Submodule.mem_top⟩⟩

/-- Universal structural identity: the concrete defect of the canonical
nonlocal graph port is zero.  No spectral parameter or zero predicate occurs. -/
@[simp] theorem arithmeticBoundaryDefect_nonlocalBoundaryPort
    (mass : arithmeticNonlocalTrace.domain) :
    arithmeticBoundaryDefect
      (arithmeticNonlocalBoundaryPortInDefectDomain mass) = 0 := by
  change arithmeticNonlocalTrace mass - arithmeticNonlocalTrace mass = 0
  exact sub_self _

/-! ## Exact finite intertwining and the global domain gate -/

/-- Finite prime-atlas version of the enriched arithmetic boundary port. -/
def finiteArithmeticNonlocalBoundaryPort
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ArithmeticEnrichedBoundaryPort :=
  (primeMassGreenBulkFiniteState (3 * M) s S,
    primeAmplitudeUpgradedMassFiniteState (3 * M) s S)

/-- The output leg of the finite arithmetic port is literally the
provenance-preserving Genuine-bracket/TFVD/Green atlas state. -/
theorem finiteArithmeticNonlocalBoundaryPort_snd_eq_enrichedReadout
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    (finiteArithmeticNonlocalBoundaryPort M s S).2 =
      canonicalEnrichedGpreLogJetGreenAtlasState M s S := by
  rw [finiteArithmeticNonlocalBoundaryPort,
    primeAmplitudeUpgradedMassFiniteState_eq_greenBulkFiniteState,
    canonicalEnrichedGpreLogJetGreenAtlasState_eq_verticalTraceFiniteState,
    primeMassGreenVerticalTraceFiniteState_eq_greenBulkFiniteState]

private theorem primeMassGreenBulkFiniteState_apply
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (p : Nat.Primes) :
    primeMassGreenBulkFiniteState M s S p =
      if p ∈ S then primeMassGreenBulkCutoffProfile M s p else 0 := by
  classical
  simp only [primeMassGreenBulkFiniteState, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

private theorem primeAmplitudeUpgradedMassFiniteState_apply
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (p : Nat.Primes) :
    primeAmplitudeUpgradedMassFiniteState M s S p =
      if p ∈ S then
        (primeCarryAmplitudeRatio p)⁻¹ *
          primeMassGreenBulkCutoffProfile M s p
      else 0 := by
  classical
  simp only [primeAmplitudeUpgradedMassFiniteState, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

/-- Every finite atlas port satisfies the nonlocal trace graph law.  Finite
support makes this statement unconditional in the spectral parameter. -/
theorem finiteArithmeticNonlocalBoundaryPort_isGraphPair
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    IsPrimeAmplitudeUpgradeGraphPair
      (finiteArithmeticNonlocalBoundaryPort M s S).1
      (finiteArithmeticNonlocalBoundaryPort M s S).2 := by
  intro p
  rw [finiteArithmeticNonlocalBoundaryPort,
    primeMassGreenBulkFiniteState_apply,
    primeAmplitudeUpgradedMassFiniteState_apply]
  by_cases hp : p ∈ S <;> simp [hp]

/-- The finite mass endpoint always belongs to the maximal global trace
domain. -/
theorem finiteArithmeticNonlocalBoundaryPort_fst_mem_traceDomain
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    (finiteArithmeticNonlocalBoundaryPort M s S).1 ∈
      arithmeticNonlocalTrace.domain := by
  rw [mem_arithmeticNonlocalTrace_domain_iff,
    ← exists_primeAmplitudeUpgradeGraphPair_iff]
  exact ⟨(finiteArithmeticNonlocalBoundaryPort M s S).2,
    finiteArithmeticNonlocalBoundaryPort_isGraphPair M s S⟩

/-- On every finite atlas, applying the closed trace to the mass endpoint
returns exactly the enriched output leg. -/
theorem arithmeticNonlocalTrace_finiteArithmeticMassEndpoint
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    arithmeticNonlocalTrace
        ⟨(finiteArithmeticNonlocalBoundaryPort M s S).1,
          finiteArithmeticNonlocalBoundaryPort_fst_mem_traceDomain M s S⟩ =
      (finiteArithmeticNonlocalBoundaryPort M s S).2 := by
  apply lp.ext
  funext p
  rw [arithmeticNonlocalTrace_apply_coordinate]
  exact (finiteArithmeticNonlocalBoundaryPort_isGraphPair M s S p).symm

/-- Complete finite structural identity: every finite arithmetic port belongs
to the fixed maximal Green-isotropic relation, before any zero is assumed. -/
theorem finiteArithmeticNonlocalBoundaryPort_mem_relation
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    finiteArithmeticNonlocalBoundaryPort M s S ∈
      arithmeticNonlocalBoundaryRelation := by
  rw [arithmeticNonlocalBoundaryRelation, operatorRelation,
    LinearPMap.mem_graph_iff]
  exact
    ⟨⟨(finiteArithmeticNonlocalBoundaryPort M s S).1,
        finiteArithmeticNonlocalBoundaryPort_fst_mem_traceDomain M s S⟩,
      rfl, arithmeticNonlocalTrace_finiteArithmeticMassEndpoint M s S⟩

/-- Coordinatewise finite intertwining.  The enriched bracket readout is the
material vertical trace flux of the mass endpoint at the aligned cutoff. -/
theorem arithmeticFiniteTrace_intertwines_enrichedBracketTfvdGreen
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s =
      primeMassGreenVerticalTraceFluxProfile (3 * M) s p :=
  finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_verticalTraceFlux p M s

/-- Domain of the closed global trace on the canonical mass state is exactly
the already identified half-amplitude regularity condition. -/
theorem primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    primeMassGreenBulkState M s hs ∈ arithmeticNonlocalTrace.domain ↔
      criticalDisplacement s.re = 0 := by
  rw [mem_arithmeticNonlocalTrace_domain_iff]
  have hfun :
      (primeMassGreenBulkState M s hs : Nat.Primes → ℝ) =
        primeMassGreenBulkCutoffProfile M s := by
    funext p
    rfl
  rw [hfun]
  exact primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff M hM hs

/-- Whenever the mass state belongs to the explicit domain, the closed trace
recovers the critical-amplitude Green profile exactly. -/
theorem arithmeticNonlocalTrace_massState_apply
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hdomain : primeMassGreenBulkState M s hs ∈
      arithmeticNonlocalTrace.domain) (p : Nat.Primes) :
    arithmeticNonlocalTrace
        ⟨primeMassGreenBulkState M s hs, hdomain⟩ p =
      primeCarryGreenBulkCutoffProfile M s p := by
  rw [arithmeticNonlocalTrace_apply_coordinate]
  change (primeCarryAmplitudeRatio p)⁻¹ *
      primeMassGreenBulkCutoffProfile M s p = _
  exact primeAmplitudeUpgrade_massBulk_eq_carryBulk M s p

/-- There is no everywhere-defined Hilbert-valued map satisfying the
prime-amplitude trace formula.  This obstruction is stronger than failure of
boundedness: an off-critical mass state would be sent to a non-`ell²` profile. -/
theorem no_everywhere_arithmeticNonlocalTrace
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : criticalDisplacement s.re ≠ 0) :
    ¬ ∃ J : ArithmeticMassCarrier → ArithmeticMassCarrier,
      ∀ mass p,
        J mass p = (primeCarryAmplitudeRatio p)⁻¹ * mass p := by
  rintro ⟨J, hJ⟩
  have hgraph : IsPrimeAmplitudeUpgradeGraphPair
      (primeMassGreenBulkState M s hs)
      (J (primeMassGreenBulkState M s hs)) := by
    intro p
    exact hJ _ p
  have hcritical :=
    (exists_primeAmplitudeUpgradeGraphPair_massState_iff M hM hs).1
      ⟨J (primeMassGreenBulkState M s hs), hgraph⟩
  exact hoff hcritical

/-- Strong vertical no-go on the completed carrier: no everywhere-defined
map can return all material trace fluxes as one prime-camera `ell²` vector.
The witness has both state and centered-bracket regularity, but its trace flux
is the nonsummable critical-amplitude profile. -/
theorem no_everywhere_globalPrimeVerticalTrace :
    ¬ ∃ J : PrimeCarryVerticalHilbert → ArithmeticMassCarrier,
      ∀ x p,
        J x p =
          (primeCarryWeightedVerticalTrace (p : ℕ) (x p)).2.re := by
  rintro ⟨J, hJ⟩
  have hsum := (lp.memℓp (J primeVerticalTraceNoGoGlobalState)).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hflux : Summable (fun p : Nat.Primes =>
      (primeVerticalTraceNoGoFluxProfile p) ^ 2) := by
    simpa [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
      Real.rpow_two, Real.norm_eq_abs, sq_abs,
      primeVerticalTraceNoGoFluxProfile,
      primeVerticalTraceNoGoGlobalState_apply, hJ] using hsum
  exact not_summable_primeVerticalTraceNoGoFluxProfile_sq hflux

/-! ## Why the finite coarse Genuine readout cannot characterize isotropy -/

/-- A two-cell provenance direction erased by coarse synthesis. -/
def finiteC3CoarseKernelWitnessVector : FiniteC3GreenBoundarySpace 2 :=
  WithLp.toLp 2 (fun n : Fin 2 => if n = 0 then 1 else -1)

/-- The complete two-leg witness retains that direction only in its first
Green leg. -/
def finiteC3CoarseKernelWitness : FiniteC3GreenPortCarrier 2 :=
  (finiteC3CoarseKernelWitnessVector, 0)

theorem finiteC3CoarseBoundaryReadout_kernelWitness :
    finiteC3CoarseBoundaryReadout 2 finiteC3CoarseKernelWitness = 0 := by
  apply Prod.ext <;>
    simp [finiteC3CoarseBoundaryReadout, finiteC3CoarseKernelWitness,
      finiteC3CoarseKernelWitnessVector, finiteC3VectorSynthesis,
      Fin.sum_univ_two]

theorem finiteC3CoarseKernelWitness_not_mem_diagonal :
    finiteC3CoarseKernelWitness ∉ finiteC3DiagonalGreenRelation 2 := by
  rw [mem_finiteC3DiagonalGreenRelation_iff]
  intro h
  have hzero := congrArg (fun x : FiniteC3GreenBoundarySpace 2 => x 0) h
  norm_num [finiteC3CoarseKernelWitness, finiteC3CoarseKernelWitnessVector] at hzero

/-- Exact finite obstruction to a defect factorization through the coarse
Genuine readout alone.  Any defect whose zero set is the fixed diagonal
relation must retain more than the two synthesized scalars. -/
theorem no_finiteC3_boundaryDefect_factorization_through_coarse
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (boundaryDefect : FiniteC3GreenPortCarrier 2 →ₗ[ℂ] Z)
    (transport : (ℂ × ℂ) →ₗ[ℂ] Z)
    (hfactor : boundaryDefect =
      transport.comp (finiteC3CoarseBoundaryReadout 2))
    (hdetect : ∀ x,
      boundaryDefect x = 0 ↔ x ∈ finiteC3DiagonalGreenRelation 2) :
    False := by
  have hdefect : boundaryDefect finiteC3CoarseKernelWitness = 0 := by
    rw [hfactor, LinearMap.comp_apply,
      finiteC3CoarseBoundaryReadout_kernelWitness, map_zero transport]
  exact finiteC3CoarseKernelWitness_not_mem_diagonal
    ((hdetect finiteC3CoarseKernelWitness).1 hdefect)

/-- The remaining arithmetic assertion that every Genuine zero supplies an
input in the domain of the nonlocal trace. -/
def GenuineZerosLieInArithmeticNonlocalTraceDomain : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    ∀ hs : s ∈ genuineCriticalStrip,
      primeMassGreenBulkState 1 s hs ∈ arithmeticNonlocalTrace.domain

/-- The remaining zero-to-domain assertion is not a bookkeeping corollary:
it is exactly the already isolated strong nonvanishing gate. -/
theorem genuineZero_to_arithmeticNonlocalTrace_domain_iff_strongNonvanishing :
    GenuineZerosLieInArithmeticNonlocalTraceDomain ↔
      GenuineStrongNonvanishingInStrip := by
  unfold GenuineZerosLieInArithmeticNonlocalTraceDomain
  constructor
  · intro hdomain s hs hoff hzero
    have hmem := hdomain hzero hs
    have hcritical :=
      (primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
        1 (by norm_num) hs).1 hmem
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
        1 (by norm_num) hs).2
    by_contra hdelta
    have hoff : s.re ≠ (1 : ℝ) / 2 := by
      intro hhalf
      apply hdelta
      unfold criticalDisplacement
      rw [hhalf]
      ring
    exact (hstrong hs hoff) hzero

end

end NativeCarryC3Crosswalk
