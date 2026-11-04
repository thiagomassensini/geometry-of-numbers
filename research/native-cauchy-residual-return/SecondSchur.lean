import FirstSurvivingCoefficient
import CarrySelfAdjointOperator.CompletedNativeRadialThreePointDeterminant
import CarrySelfAdjointOperator.CompletedNativeSixthOrderThetaPositivity

/-!
# Second Schur limit for the unchanged three-source Cauchy kernel

The physical matrix below is the same raw Cauchy defect already used in the
first-survivor development.  This file connects its three-point determinant
to the existing native radial Green determinant, keeping the characteristic
and the chiral quotient as the source.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace CarryCauchyResidual

open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The original physical Cauchy matrix on the first `N` radial sources. -/
def nativePhysicalCauchyMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => nativeRawKernel k i.val j.val

/-- Its first three principal determinants, with the original Cauchy scale. -/
def nativePhysicalD1 (k : ℕ) : ℂ := nativeRawKernel k 0 0

def nativePhysicalD2 (k : ℕ) : ℂ :=
  (nativePhysicalCauchyMatrix k 2).det

def nativePhysicalD3 (k : ℕ) : ℂ :=
  (nativePhysicalCauchyMatrix k 3).det

def nativePhysicalP0 (k : ℕ) : ℂ := nativePhysicalD1 k

def nativePhysicalP1 (k : ℕ) : ℂ := nativePhysicalD2 k / nativePhysicalD1 k

def nativePhysicalP2 (k : ℕ) : ℂ :=
  nativePhysicalD3 k / nativePhysicalD2 k

private def nativePhysicalFinThreeBlockEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3 :=
  { toFun := Sum.elim (Fin.castAdd 1) (Fin.natAdd 2)
    invFun := @Fin.addCases 2 1 (fun _ => Fin 2 ⊕ Fin 1) Sum.inl Sum.inr
    left_inv := by rintro (i | i) <;> simp
    right_inv := by
      intro i
      refine Fin.addCases (m := 2) (n := 1) ?_ ?_ i <;> intro j <;> simp }

/-- The untouched raw Cauchy defect is Hermitian by symmetry of the original
Cauchy factor and the two conjugate return factors. -/
theorem nativeRawKernel_hermitian_entry (k i j : ℕ) :
    star (nativeRawKernel k j i) = nativeRawKernel k i j := by
  unfold nativeRawKernel
  have hc : cauchy k j i = cauchy k i j := by
    simp [cauchy]
    ring
  have hcs : star (cauchy k i j) = cauchy k i j := by
    simp [cauchy]
  have hdef : 1 - star (sourceReturn k j) * sourceReturn k i =
      star (1 - star (sourceReturn k i) * sourceReturn k j) := by
    simp
    ring
  have hdef' : star (1 - star (sourceReturn k j) * sourceReturn k i) =
      1 - star (sourceReturn k i) * sourceReturn k j := by
    rw [hdef]
    simp
  calc
    star (cauchy k j i *
        (1 - star (sourceReturn k j) * sourceReturn k i)) =
        star (cauchy k i j) *
          star (1 - star (sourceReturn k j) * sourceReturn k i) := by rw [hc]; simp
    _ = cauchy k i j *
        (1 - star (sourceReturn k i) * sourceReturn k j) := by rw [hcs, hdef']

/-- Every finite raw physical matrix is Hermitian. -/
theorem nativePhysicalCauchyMatrix_isHermitian (k N : ℕ) :
    (nativePhysicalCauchyMatrix k N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (nativeRawKernel k j.val i.val) = nativeRawKernel k i.val j.val
  exact nativeRawKernel_hermitian_entry k i.val j.val

private theorem nativePhysicalDeterminant_star (k N : ℕ) :
    star ((nativePhysicalCauchyMatrix k N).det) =
      (nativePhysicalCauchyMatrix k N).det := by
  have hM := nativePhysicalCauchyMatrix_isHermitian k N
  have hdet := congrArg Matrix.det hM.eq
  rw [Matrix.det_conjTranspose] at hdet
  exact hdet

theorem nativePhysicalD1_star (k : ℕ) : star (nativePhysicalD1 k) =
    nativePhysicalD1 k := by
  unfold nativePhysicalD1
  have h := nativeRawKernel_hermitian_entry k 0 0
  simpa using h

theorem nativePhysicalD2_star (k : ℕ) : star (nativePhysicalD2 k) =
    nativePhysicalD2 k := by
  simpa [nativePhysicalD2] using nativePhysicalDeterminant_star k 2

theorem nativePhysicalD3_star (k : ℕ) : star (nativePhysicalD3 k) =
    nativePhysicalD3 k := by
  simpa [nativePhysicalD3] using nativePhysicalDeterminant_star k 3

/-- The physical second successive Schur pivot.  The quotient is total; its
eventual denominator nonvanishing is proved from the positive D2 limit. -/
def nativePhysicalSecondSchurPivot (k : ℕ) : ℂ :=
  nativePhysicalD3 k / nativePhysicalD2 k

/-- Real Cayley coordinate extracted from the original completed
logarithmic derivative on the positive imaginary axis. -/
def nativePhysicalCayleyRho (s : ℝ) : ℂ :=
  2 * (s : ℂ) * completedNativeLogDerivative (-((s : ℂ)^2))

/-- Real spacing of the original shifted radial source grid. -/
def nativePhysicalRadialCoordinate (k i : ℕ) : ℝ :=
  ((i + 1 : ℕ) : ℝ) * canonicalGreenJetRealStep k

/-- The reduced logarithmic derivative is real on the small real interval:
its actual convergent Taylor series has the canonical real moments as
coefficients. -/
theorem completedNativeLogDerivative_real_eventually :
    ∀ᶠ s : ℝ in nhds 0,
      star (completedNativeLogDerivative (-((s : ℂ)^2))) =
        completedNativeLogDerivative (-((s : ℂ)^2)) := by
  have harg : Tendsto (fun s : ℝ => -((s : ℂ)^2)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ => -((s : ℂ)^2)) 0 := by fun_prop
    have h := hcont.tendsto
    simpa using h
  filter_upwards [harg.eventually
    completedNativeLogDerivative_eventually_hasSum_canonical] with s hsum
  let u : ℂ := -((s : ℂ)^2)
  have hu : u = ((-(s^2) : ℝ) : ℂ) := by
    dsimp [u]
    norm_num
  have him : (completedNativeLogDerivative u).im = 0 := by
    have hsumEq := hsum.tsum_eq
    have himEq := congrArg Complex.im hsumEq
    rw [Complex.im_tsum hsum.summable] at himEq
    have hterms : ∀ n : ℕ, (u^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ)).im = 0 := by
      intro n
      have hterm : u^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) =
          (((-(s^2) : ℝ)^n * canonicalCompletedNativeLogDerivativeMoment n : ℝ) : ℂ) := by
        rw [hu]
        norm_num
      rw [hterm]
      rw [Complex.ofReal_im]
    have hsumIm : (∑' n : ℕ,
        (u^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ)).im) = 0 := by
      simp only [hterms, tsum_zero]
    calc
      (completedNativeLogDerivative u).im =
          ∑' n : ℕ,
            (u^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ)).im := himEq.symm
      _ = 0 := hsumIm
  have hreal : star (completedNativeLogDerivative u) =
      completedNativeLogDerivative u := by
    apply Complex.ext
    · simp
    · simp [him]
  simpa only [u] using hreal

/-- On the imaginary radial axis, the original operator logarithmic
derivative is exactly the Cayley coordinate `i rho(s)`. -/
theorem nativePhysicalCayleyRho_eq_nativeTransverseLogSlope_eventually :
    ∀ᶠ s : ℝ in nhds 0,
      nativePhysicalCayleyRho s = nativeTransverseLogSlope (s : ℂ) := by
  have hcurve : Tendsto (fun s : ℝ => Complex.I * (s : ℂ))
      (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ => Complex.I * (s : ℂ)) 0 := by fun_prop
    have h := hcont.tendsto
    simpa using h
  filter_upwards [hcurve.eventually
    completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate] with s hs
  have hs' : completedNativeOperatorLogDerivative (Complex.I * (s : ℂ)) =
      2 * (Complex.I * (s : ℂ)) *
        completedNativeLogDerivative ((Complex.I * (s : ℂ))^2) := by
    exact hs
  unfold nativePhysicalCayleyRho nativeTransverseLogSlope
  rw [hs']
  have hsquare : (Complex.I * (s : ℂ))^2 = -((s : ℂ)^2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsquare]
  have hI : -Complex.I * (2 * (Complex.I * (s : ℂ))) = 2 * (s : ℂ) := by
    calc
      -Complex.I * (2 * (Complex.I * (s : ℂ))) =
          -2 * Complex.I ^ 2 * (s : ℂ) := by ring
      _ = 2 * (s : ℂ) := by rw [Complex.I_sq]; ring
  calc
    2 * (s : ℂ) * completedNativeLogDerivative (-((s : ℂ)^2)) =
        (-Complex.I * (2 * (Complex.I * (s : ℂ)))) *
          completedNativeLogDerivative (-((s : ℂ)^2)) := by rw [hI]
    _ = -Complex.I * (2 * (Complex.I * (s : ℂ)) *
        completedNativeLogDerivative (-((s : ℂ)^2))) := by ring

/-- The Cayley coordinate is real locally, because the full moment series
is real there. -/
theorem nativePhysicalCayleyRho_real_eventually :
    ∀ᶠ s : ℝ in nhds 0,
      star (nativePhysicalCayleyRho s) = nativePhysicalCayleyRho s := by
  filter_upwards [completedNativeLogDerivative_real_eventually] with s hs
  simp [nativePhysicalCayleyRho, hs]

private theorem nativeCayley_negSq_pow (z : ℂ) (n : ℕ) :
    (-(z^2))^n = (-1:ℂ)^n * z^(2*n) := by
  rw [show -(z^2) = (-1:ℂ) * z^2 by ring, mul_pow, pow_mul]

/-- The full, locally convergent series for the Cayley coordinate uses the
canonical moments from the characteristic logarithmic derivative. -/
theorem nativePhysicalCayleyRho_hasSum_eventually :
    ∀ᶠ s : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
        2 * (s : ℂ) * (-(s : ℂ)^2)^n *
          (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
        (nativePhysicalCayleyRho s) := by
  have harg : Tendsto (fun s : ℝ => -((s : ℂ)^2)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ => -((s : ℂ)^2)) 0 := by fun_prop
    simpa using hcont.tendsto
  filter_upwards [harg.eventually
    completedNativeLogDerivative_eventually_hasSum_canonical] with s hsum
  have hscaled := hsum.mul_left (2 * (s : ℂ))
  have hscaled' : HasSum (fun n : ℕ =>
      2 * (s : ℂ) * (-(s : ℂ)^2)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (nativePhysicalCayleyRho s) := by
    simpa [nativePhysicalCayleyRho, mul_assoc] using hscaled
  exact hscaled'

/-- The analytic two-variable Cayley kernel and the exact nth moment term. -/
def nativePhysicalCayleyAnalyticKernel (s t : ℝ) : ℂ :=
  2 * (nativePhysicalCayleyRho s + nativePhysicalCayleyRho t) /
    ((s + t : ℝ) : ℂ)

def nativePhysicalCayleyAnalyticMomentTerm (s t : ℝ) (n : ℕ) : ℂ :=
  4 * (-1:ℂ)^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) *
    (((s : ℂ)^(2*n+1) + (t : ℂ)^(2*n+1)) /
      ((s + t : ℝ) : ℂ))

/-- The same nth coefficient after substituting the actual shifted radial
mesh points `s_i=(i+1)/(k+1)`. -/
def nativePhysicalCayleyPhysicalMomentTerm (k i j n : ℕ) : ℂ :=
  4 * (-1:ℂ)^n * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) *
    ((((i + 1 : ℕ) : ℂ)^(2*n+1) +
      ((j + 1 : ℕ) : ℂ)^(2*n+1)) /
        ((i + j + 2 : ℕ) : ℂ)) *
    (canonicalGreenJetRealStep k : ℂ)^(2*n)

private theorem nativePhysicalCayleyAnalyticMomentTerm_eq_physical
    (k i j n : ℕ) :
    nativePhysicalCayleyAnalyticMomentTerm
        (nativePhysicalRadialCoordinate k i)
        (nativePhysicalRadialCoordinate k j) n =
      nativePhysicalCayleyPhysicalMomentTerm k i j n := by
  let xi : ℂ := ((i + 1 : ℕ) : ℂ)
  let xj : ℂ := ((j + 1 : ℕ) : ℂ)
  let eps : ℂ := (canonicalGreenJetRealStep k : ℂ)
  have heps : eps ≠ 0 := by
    dsimp [eps]
    apply Complex.ofReal_ne_zero.mpr
    unfold canonicalGreenJetRealStep
    positivity
  have hxi : (nativePhysicalRadialCoordinate k i : ℂ) = xi * eps := by
    rw [nativePhysicalRadialCoordinate, Complex.ofReal_mul]
    dsimp [xi, eps]
  have hxj : (nativePhysicalRadialCoordinate k j : ℂ) = xj * eps := by
    rw [nativePhysicalRadialCoordinate, Complex.ofReal_mul]
    dsimp [xj, eps]
  have hsum : ((nativePhysicalRadialCoordinate k i +
      nativePhysicalRadialCoordinate k j : ℝ) : ℂ) =
      ((i + j + 2 : ℕ) : ℂ) * eps := by
    rw [Complex.ofReal_add, hxi, hxj]
    dsimp [xi, xj, eps]
    push_cast
    ring
  have hden : ((i + j + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (i + j + 2 : ℝ) ≠ 0 by positivity)
  have hpowxi : (xi * eps)^(2*n+1) = xi^(2*n+1) * eps^(2*n+1) := by
    rw [mul_pow]
  have hpowxj : (xj * eps)^(2*n+1) = xj^(2*n+1) * eps^(2*n+1) := by
    rw [mul_pow]
  unfold nativePhysicalCayleyAnalyticMomentTerm
    nativePhysicalCayleyPhysicalMomentTerm
  rw [hxi, hxj, hsum, hpowxi, hpowxj, pow_succ]
  dsimp [xi, xj]
  field_simp [heps, hden]
  simp only [Nat.mul_comm]
  ring

/-- In a neighborhood of the origin, the analytic Cayley kernel is the
convergent two-variable series whose coefficients are exactly the canonical
logarithmic-derivative moments. -/
theorem nativePhysicalCayleyAnalyticKernel_hasSum
    (s t : ℝ)
    (hs : HasSum (fun n : ℕ =>
      2 * (s : ℂ) * (-(s : ℂ)^2)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (nativePhysicalCayleyRho s))
    (ht : HasSum (fun n : ℕ =>
      2 * (t : ℂ) * (-(t : ℂ)^2)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (nativePhysicalCayleyRho t))
    (hst : s + t ≠ 0) :
    HasSum (fun n : ℕ => nativePhysicalCayleyAnalyticMomentTerm s t n)
      (nativePhysicalCayleyAnalyticKernel s t) := by
  let denominator : ℂ := ((s + t : ℝ) : ℂ)
  have hden : denominator ≠ 0 := by
    dsimp [denominator]
    exact Complex.ofReal_ne_zero.mpr hst
  have hsum := (hs.add ht).mul_left (2 / denominator)
  have hsum' : HasSum (fun n : ℕ =>
      (2 / denominator) *
        (2 * (s : ℂ) * (-(s : ℂ)^2)^n *
          (canonicalCompletedNativeLogDerivativeMoment n : ℂ) +
        2 * (t : ℂ) * (-(t : ℂ)^2)^n *
          (canonicalCompletedNativeLogDerivativeMoment n : ℂ)))
      (nativePhysicalCayleyAnalyticKernel s t) := by
    convert hsum using 1
    · rfl
    · dsimp [nativePhysicalCayleyAnalyticKernel, denominator]
      field_simp
  refine HasSum.congr_fun hsum' (fun n => ?_)
  dsimp [nativePhysicalCayleyAnalyticMomentTerm]
  have hpowS : (-(s : ℂ)^2)^n = (-1:ℂ)^n * (s : ℂ)^(2*n) :=
    nativeCayley_negSq_pow (s : ℂ) n
  have hpowT : (-(t : ℂ)^2)^n = (-1:ℂ)^n * (t : ℂ)^(2*n) :=
    nativeCayley_negSq_pow (t : ℂ) n
  have hoddS : (s : ℂ)^(2*n+1) = (s : ℂ)^(2*n) * (s : ℂ) := by
    rw [pow_add, pow_one]
  have hoddT : (t : ℂ)^(2*n+1) = (t : ℂ)^(2*n) * (t : ℂ) := by
    rw [pow_add, pow_one]
  rw [hpowS, hpowT, hoddS, hoddT]
  dsimp [denominator]
  field_simp [hden]
  ring

/-- The coefficient series converges for every pair of sufficiently small
real arguments, and its denominator is kept explicit. -/
theorem nativePhysicalCayleyAnalyticKernel_hasSum_eventually :
    ∀ᶠ s : ℝ in nhds 0, ∀ᶠ t : ℝ in nhds 0,
      s + t ≠ 0 →
        HasSum (fun n : ℕ => nativePhysicalCayleyAnalyticMomentTerm s t n)
          (nativePhysicalCayleyAnalyticKernel s t) := by
  filter_upwards [nativePhysicalCayleyRho_hasSum_eventually] with s hs
  filter_upwards [nativePhysicalCayleyRho_hasSum_eventually] with t ht hst
  exact nativePhysicalCayleyAnalyticKernel_hasSum s t hs ht hst

/-- The actual chiral return on the imaginary radial line is the Cayley
transform of the real coordinate; the denominator is certified nonzero on
the same local neighborhood. -/
theorem nativePhysicalCayleyRho_cayley_eventually :
    ∀ᶠ s : ℝ in nhds 0,
      nativeTransverseChiralQuotient (s : ℂ) =
          (nativePhysicalCayleyRho s - 1) /
            (nativePhysicalCayleyRho s + 1) ∧
        nativePhysicalCayleyRho s + 1 ≠ 0 ∧
          star (nativePhysicalCayleyRho s) = nativePhysicalCayleyRho s := by
  have hrealcast : Tendsto (fun s : ℝ => (s : ℂ)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℝ => (s : ℂ)) 0 := by fun_prop
    exact hcont.tendsto
  filter_upwards [hrealcast.eventually
      nativeTransverseChiralQuotient_eq_cayley_eventually,
    nativePhysicalCayleyRho_eq_nativeTransverseLogSlope_eventually,
    nativePhysicalCayleyRho_real_eventually] with s hq hρ hreal
  rcases hq with ⟨hq, hden⟩
  rw [← hρ] at hq hden
  exact ⟨hq, hden, hreal⟩

theorem nativePhysicalRadialPoint_eq (k i : ℕ) :
    canonicalCompletedC3RadialTiltPoint k i =
      Complex.I * (nativePhysicalRadialCoordinate k i : ℂ) := by
  simp only [canonicalCompletedC3RadialTiltPoint,
    canonicalCompletedC3RadialTiltStep, nativePhysicalRadialCoordinate,
    ]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [← canonicalGreenJetRealStep_coe]
  push_cast
  ring

/-- The real diagonal Cayley factor attached to a physical source. -/
def nativePhysicalCayleyFactor (k i : ℕ) : ℂ :=
  1 + nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i)

/-- Entrywise diagonal congruence of the unchanged raw physical kernel. -/
def nativePhysicalCayleyCongruenceEntry (k i j : ℕ) : ℂ :=
  nativePhysicalCayleyFactor k i * nativeRawKernel k i j *
    nativePhysicalCayleyFactor k j

/-- The sampled physical matrix after the diagonal Cayley congruence. -/
def nativePhysicalCayleyMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i : Fin N => nativePhysicalCayleyFactor k i.val) *
    nativePhysicalCauchyMatrix k N *
      Matrix.diagonal (fun i : Fin N => nativePhysicalCayleyFactor k i.val)

theorem nativePhysicalCayleyMatrix_apply (k N : ℕ) (i j : Fin N) :
    nativePhysicalCayleyMatrix k N i j =
      nativePhysicalCayleyCongruenceEntry k i.val j.val := by
  simp [nativePhysicalCayleyMatrix, nativePhysicalCayleyCongruenceEntry,
    nativePhysicalCauchyMatrix, Matrix.mul_apply, Matrix.diagonal_apply]

/-- At each fixed source, the original return is eventually the Cayley value
of the real native logarithmic derivative coordinate. -/
theorem sourceReturn_eq_nativePhysicalCayley_eventually (i : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      sourceReturn k i =
          (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) - 1) /
            (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) + 1) ∧
        nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) + 1 ≠ 0 ∧
          star (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i)) =
            nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) := by
  have hstep := canonicalGreenJetRealStep_tendsto_zero
  have hs : Tendsto (fun k : ℕ => nativePhysicalRadialCoordinate k i)
      atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds (x := ((i + 1 : ℕ) : ℝ))).mul hstep
    simpa [nativePhysicalRadialCoordinate] using hmul
  filter_upwards [hs.eventually nativePhysicalCayleyRho_cayley_eventually] with k hk
  have hpoint := nativePhysicalRadialPoint_eq k i
  have hq : sourceReturn k i =
      nativeTransverseChiralQuotient
        (nativePhysicalRadialCoordinate k i : ℂ) := by
    simp only [sourceReturn, nativeTransverseChiralQuotient, hpoint]
  rw [← hq] at hk
  exact hk

/-- On every fixed finite source block, the Cayley factors are eventually
real and nonzero, with both facts proved from the original characteristic. -/
theorem nativePhysicalCayleyFactor_finite_eventually_real_nonzero (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
      star (nativePhysicalCayleyFactor k i.val) =
          nativePhysicalCayleyFactor k i.val ∧
        nativePhysicalCayleyFactor k i.val ≠ 0 := by
  have hi (i : Fin N) : ∀ᶠ k : ℕ in atTop,
      star (nativePhysicalCayleyFactor k i.val) =
          nativePhysicalCayleyFactor k i.val ∧
        nativePhysicalCayleyFactor k i.val ≠ 0 := by
    filter_upwards [sourceReturn_eq_nativePhysicalCayley_eventually i.val] with k hk
    rcases hk with ⟨_, hden, hreal⟩
    dsimp [nativePhysicalCayleyFactor]
    constructor
    · have hreal' : (starRingEnd ℂ)
          (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i.val)) =
            nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i.val) := hreal
      rw [map_add, map_one, hreal']
    · simpa [add_comm] using hden
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.univ : Finset (Fin N)).eventually_all.2
      (fun i _ => hi i)

/-- Exact algebraic Cayley congruence for the raw Cauchy kernel, on the
eventual local domain of the original characteristic. -/
theorem nativePhysicalCayleyCongruenceEntry_eq_eventually (i j : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      nativePhysicalCayleyCongruenceEntry k i j =
        2 * cauchy k i j *
          (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) +
            nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k j)) := by
  filter_upwards [sourceReturn_eq_nativePhysicalCayley_eventually i,
    sourceReturn_eq_nativePhysicalCayley_eventually j] with k hi hj
  rcases hi with ⟨hqi, hdi, hri⟩
  rcases hj with ⟨hqj, hdj, hrj⟩
  have hqistar : star (sourceReturn k i) = sourceReturn k i := by
    rw [hqi]
    simp [hri]
  have hqistar' : (starRingEnd ℂ) (sourceReturn k i) = sourceReturn k i := by
    simpa only [starRingEnd_apply] using hqistar
  let ri := nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i)
  let rj := nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k j)
  have hdi' : ri + 1 ≠ 0 := by simpa [ri] using hdi
  have hdj' : rj + 1 ≠ 0 := by simpa [rj] using hdj
  have hri' : star ri = ri := by simpa [ri] using hri
  have hrj' : star rj = rj := by simpa [rj] using hrj
  dsimp [nativePhysicalCayleyCongruenceEntry, nativePhysicalCayleyFactor,
    nativeRawKernel]
  rw [hqistar', hqi, hqj]
  field_simp [hdi, hdj]
  ring

/-- The original Cauchy denominator is exactly the reciprocal sum of the two
physical radial coordinates. -/
theorem nativePhysicalCauchy_eq_inv_radialSum (k i j : ℕ) :
    cauchy k i j =
      ((nativePhysicalRadialCoordinate k i +
        nativePhysicalRadialCoordinate k j : ℝ) : ℂ)⁻¹ := by
  unfold cauchy nativePhysicalRadialCoordinate canonicalGreenJetRealStep
  push_cast
  field_simp
  ring

/-- Thus the exact diagonal Cayley congruence is the analytic kernel
`2 (rho(s)+rho(t))/(s+t)` at the same physical sample points. -/
theorem nativePhysicalCayleyCongruenceEntry_eq_analyticKernel_eventually
    (i j : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      nativePhysicalCayleyCongruenceEntry k i j =
        nativePhysicalCayleyAnalyticKernel
          (nativePhysicalRadialCoordinate k i)
          (nativePhysicalRadialCoordinate k j) := by
  filter_upwards [nativePhysicalCayleyCongruenceEntry_eq_eventually i j] with k hk
  rw [nativePhysicalCauchy_eq_inv_radialSum] at hk
  dsimp [nativePhysicalCayleyAnalyticKernel]
  calc
    nativePhysicalCayleyCongruenceEntry k i j =
        2 * ((nativePhysicalRadialCoordinate k i +
          nativePhysicalRadialCoordinate k j : ℝ) : ℂ)⁻¹ *
          (nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k i) +
            nativePhysicalCayleyRho (nativePhysicalRadialCoordinate k j)) := hk
    _ = _ := by ring

/-- The entrywise Cayley congruence of the original physical kernel has the
full convergent moment expansion on the same shifted radial grid. -/
theorem nativePhysicalCayleyCongruenceEntry_hasSum_eventually (i j : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      HasSum (fun n : ℕ =>
        nativePhysicalCayleyPhysicalMomentTerm k i j n)
        (nativePhysicalCayleyCongruenceEntry k i j) := by
  have hstep := canonicalGreenJetRealStep_tendsto_zero
  have hsi : Tendsto (fun k : ℕ => nativePhysicalRadialCoordinate k i)
      atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds (x := ((i + 1 : ℕ) : ℝ))).mul hstep
    simpa [nativePhysicalRadialCoordinate] using hmul
  have hsj : Tendsto (fun k : ℕ => nativePhysicalRadialCoordinate k j)
      atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds (x := ((j + 1 : ℕ) : ℝ))).mul hstep
    simpa [nativePhysicalRadialCoordinate] using hmul
  have hseriesi := hsi.eventually nativePhysicalCayleyRho_hasSum_eventually
  have hseriesj := hsj.eventually nativePhysicalCayleyRho_hasSum_eventually
  filter_upwards [hseriesi, hseriesj,
    nativePhysicalCayleyCongruenceEntry_eq_analyticKernel_eventually i j]
    with k hi hj hentry
  have hst : nativePhysicalRadialCoordinate k i +
      nativePhysicalRadialCoordinate k j ≠ 0 := by
    have hposi : 0 < nativePhysicalRadialCoordinate k i := by
      unfold nativePhysicalRadialCoordinate canonicalGreenJetRealStep
      positivity
    have hposj : 0 < nativePhysicalRadialCoordinate k j := by
      unfold nativePhysicalRadialCoordinate canonicalGreenJetRealStep
      positivity
    exact ne_of_gt (add_pos hposi hposj)
  have hkernel := nativePhysicalCayleyAnalyticKernel_hasSum
    (nativePhysicalRadialCoordinate k i)
    (nativePhysicalRadialCoordinate k j) hi hj hst
  have hsumEntry : HasSum
      (fun n : ℕ => nativePhysicalCayleyAnalyticMomentTerm
        (nativePhysicalRadialCoordinate k i)
        (nativePhysicalRadialCoordinate k j) n)
      (nativePhysicalCayleyCongruenceEntry k i j) := by
    rw [hentry]
    exact hkernel
  exact HasSum.congr_fun hsumEntry (fun n =>
    (nativePhysicalCayleyAnalyticMomentTerm_eq_physical k i j n).symm)

/-- Checkpoint 2, finite-matrix form: the entrywise diagonal congruence of the
original Cauchy matrix has the full canonical-moment expansion on the same
physical radial grid. -/
theorem nativePhysicalCayleyMatrix_hasSum_eventually (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ i j : Fin N,
      HasSum (fun n : ℕ =>
        nativePhysicalCayleyPhysicalMomentTerm k i.val j.val n)
        (nativePhysicalCayleyMatrix k N i j) := by
  have hij (i j : Fin N) :=
    nativePhysicalCayleyCongruenceEntry_hasSum_eventually i.val j.val
  have hj (i : Fin N) : ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      HasSum (fun n : ℕ =>
        nativePhysicalCayleyPhysicalMomentTerm k i.val j.val n)
        (nativePhysicalCayleyMatrix k N i j) := by
    have h := (Finset.univ : Finset (Fin N)).eventually_all.2
      (fun j _ => (hij i j).mono fun k hk => by
        simpa only [← nativePhysicalCayleyMatrix_apply] using hk)
    simpa only [Finset.mem_univ, forall_true_left] using h
  have h := (Finset.univ : Finset (Fin N)).eventually_all.2
    (fun i _ => hj i)
  simpa only [Finset.mem_univ, forall_true_left] using h

/-- The exact matrix congruence agrees entrywise with the analytic Cayley
kernel at every point of each fixed finite grid, eventually in the cutoff. -/
theorem nativePhysicalCayleyMatrix_eq_analyticKernel_eventually (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ i j : Fin N,
      nativePhysicalCayleyMatrix k N i j =
        nativePhysicalCayleyAnalyticKernel
          (nativePhysicalRadialCoordinate k i.val)
          (nativePhysicalRadialCoordinate k j.val) := by
  have hij (i j : Fin N) :=
    nativePhysicalCayleyCongruenceEntry_eq_analyticKernel_eventually i.val j.val
  have hj (i : Fin N) : ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      nativePhysicalCayleyMatrix k N i j =
        nativePhysicalCayleyAnalyticKernel
          (nativePhysicalRadialCoordinate k i.val)
          (nativePhysicalRadialCoordinate k j.val) := by
    have h := (Finset.univ : Finset (Fin N)).eventually_all.2
      (fun j _ => (hij i j).mono fun k hk => by
        simpa only [← nativePhysicalCayleyMatrix_apply] using hk)
    simpa only [Finset.mem_univ, forall_true_left] using h
  have h := (Finset.univ : Finset (Fin N)).eventually_all.2
    (fun i _ => hj i)
  simpa only [Finset.mem_univ, forall_true_left] using h

private def nativePhysicalAmplitude (k n : ℕ) : ℂ :=
  completedNativeNormalizedPositiveChiralAmplitude
    (canonicalCompletedC3RadialTiltPoint k n)

private def nativePhysicalAmplitudeNormProduct (k : ℕ) : ℂ :=
  ∏ i : Fin 3, star (nativePhysicalAmplitude k i.val) *
    nativePhysicalAmplitude k i.val

/-- Every physical source carries the same central amplitude fixed by the
original characteristic normalization. -/
theorem nativePhysicalAmplitude_tendsto (n : ℕ) :
    Tendsto (fun k => nativePhysicalAmplitude k n) atTop
      (nhds (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)))) := by
  have hF := completedNativeOperatorCharacteristic_analyticAt
    zero_mem_completedNativeHeightDomain
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hFderiv0 : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have hAmplitude : ContinuousAt completedNativeNormalizedPositiveChiralAmplitude 0 := by
    unfold completedNativeNormalizedPositiveChiralAmplitude
    have hnormalizer : AnalyticAt ℂ
        canonicalCompletedC3FullWronskianChiralNormalization 0 := by
      unfold canonicalCompletedC3FullWronskianChiralNormalization
      have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
      exact (analyticAt_const.mul hF).inv
        (mul_ne_zero hsqrt hF0)
    have hpositive : AnalyticAt ℂ
        completedNativePositiveHermiteBiehlerCoordinate 0 := by
      unfold completedNativePositiveHermiteBiehlerCoordinate
      exact hF.deriv.neg.add (analyticAt_const.mul hF)
    exact hnormalizer.mul hpositive |>.continuousAt
  have hpoint := canonicalCompletedC3RadialTiltPoint_tendsto_zero n
  have hAmplitudeLimit := hAmplitude.tendsto.comp hpoint
  have hAmplitudeZero : completedNativeNormalizedPositiveChiralAmplitude 0 =
      Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) := by
    unfold completedNativeNormalizedPositiveChiralAmplitude
      canonicalCompletedC3FullWronskianChiralNormalization
      completedNativePositiveHermiteBiehlerCoordinate
    simp [hFderiv0]
    field_simp [hF0]
  simpa only [Function.comp_def, nativePhysicalAmplitude, hAmplitudeZero] using
    hAmplitudeLimit

/-- The raw Cauchy defect is exactly the existing radial chiral Pick matrix.
The Cauchy denominator and radial separation are the same `k+1`, `i+j+2`
data; no new kernel is substituted. -/
theorem nativePhysicalCauchyMatrix_eq_nativePick (k N : ℕ) :
    nativePhysicalCauchyMatrix k N =
      canonicalCompletedNativeRadialChiralPickSampleMatrix k N := by
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]
  ext i j
  rw [nativePhysicalCauchyMatrix, Matrix.of_apply,
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  simp only [nativeRawKernel, cauchy, sourceReturn,
    canonicalCompletedC3RadialTiltPoint]
  push_cast
  rw [div_eq_mul_inv]
  simp only [starRingEnd_apply]

/-- Exact determinant transport from the source Pick matrix to the native
`dslope` determinant. The only scalar factor is the already certified
positive-channel amplitude in the existing realization. -/
theorem nativePhysicalD3_eq_scaled_dslope_det (k : ℕ)
    (hregular : ∀ i : Fin 3,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    nativePhysicalD3 k =
      8 * (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
        nativePhysicalAmplitudeNormProduct k := by
  let amplitude : Fin 3 → ℂ := fun i => nativePhysicalAmplitude k i.val
  let diagonal := Matrix.diagonal amplitude
  have hcong := canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
    k 3 hregular
  rw [← nativePhysicalCauchyMatrix_eq_nativePick k 3] at hcong
  have hcong' : canonicalCompletedNativeRadialDslopeSampleMatrix k 3 =
      (2:ℂ)⁻¹ • (diagonal.conjTranspose *
        nativePhysicalCauchyMatrix k 3 * diagonal) := by
    rw [hcong]
    ext i j
    simp [diagonal, amplitude, nativePhysicalAmplitude,
      Matrix.smul_apply, Complex.real_smul]
  have hdet := congrArg Matrix.det hcong'
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose] at hdet
  simp only [nativePhysicalD3, nativePhysicalCauchyMatrix] at hdet ⊢
  simp [diagonal, Matrix.det_diagonal] at hdet
  have hstarprod : star (∏ i : Fin 3, amplitude i) =
      ∏ i : Fin 3, star (amplitude i) := by
    simpa only [starRingEnd_apply] using
      (map_prod (starRingEnd ℂ) amplitude Finset.univ)
  have hAmpProd : star (∏ i : Fin 3, amplitude i) *
      ∏ i : Fin 3, amplitude i = nativePhysicalAmplitudeNormProduct k := by
    calc
      star (∏ i : Fin 3, amplitude i) * ∏ i : Fin 3, amplitude i =
          (∏ i : Fin 3, star (amplitude i)) * ∏ i : Fin 3, amplitude i := by
            rw [hstarprod]
      _ = ∏ i : Fin 3, star (amplitude i) * amplitude i := by
            simp only [Finset.prod_mul_distrib]
      _ = nativePhysicalAmplitudeNormProduct k := by
            simp [nativePhysicalAmplitudeNormProduct, amplitude]
  have hfactor : (∏ i : Fin 3, star (amplitude i)) *
      (Matrix.of fun i j : Fin 3 => nativeRawKernel k i.val j.val).det *
        ∏ i : Fin 3, amplitude i =
      nativePhysicalAmplitudeNormProduct k *
        (Matrix.of fun i j : Fin 3 => nativeRawKernel k i.val j.val).det := by
    rw [← hstarprod]
    calc
      star (∏ i : Fin 3, amplitude i) *
          (Matrix.of fun i j : Fin 3 => nativeRawKernel k i.val j.val).det *
          ∏ i : Fin 3, amplitude i =
        (star (∏ i : Fin 3, amplitude i) * ∏ i : Fin 3, amplitude i) *
          (Matrix.of fun i j : Fin 3 => nativeRawKernel k i.val j.val).det := by ring
      _ = _ := by rw [hAmpProd]
  simp only [starRingEnd_apply] at hdet
  rw [hfactor] at hdet
  norm_num at hdet
  have hprod : nativePhysicalAmplitudeNormProduct k ≠ 0 := by
    unfold nativePhysicalAmplitudeNormProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply mul_ne_zero
    · exact (map_ne_zero (starRingEnd ℂ)).mpr
        (completedNativeNormalizedPositiveChiralAmplitude_ne_zero
          (hregular i).2.1 (hregular i).2.2)
    · exact completedNativeNormalizedPositiveChiralAmplitude_ne_zero
        (hregular i).2.1 (hregular i).2.2
  have hdetScaled := hdet
  field_simp at hdetScaled
  have hdet' : nativePhysicalAmplitudeNormProduct k * nativePhysicalD3 k =
      8 * (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det := by
    simpa [nativePhysicalD3, nativePhysicalCauchyMatrix,
      mul_comm, mul_left_comm, mul_assoc] using hdetScaled.symm
  field_simp [hprod]
  calc
    nativePhysicalD3 k * nativePhysicalAmplitudeNormProduct k =
        nativePhysicalAmplitudeNormProduct k * nativePhysicalD3 k := by ring
    _ = 8 * (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det := hdet'

/-- The three native channel amplitudes tend to their common central
normalization, so their squared product tends to `1/8`. -/
theorem nativePhysicalAmplitudeNormProduct_tendsto :
    Tendsto nativePhysicalAmplitudeNormProduct atTop (nhds (1/8:ℂ)) := by
  have hII : -Complex.I * Complex.I = (1:ℂ) := by
    calc
      -Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
      _ = -(Complex.I ^ 2) := by rw [pow_two]
      _ = 1 := by rw [Complex.I_sq]; norm_num
  have hcenter' : -(Complex.I * PhysicalSewing.portHalfNormalization *
      (Complex.I * PhysicalSewing.portHalfNormalization)) = (1/2:ℂ) := by
    calc
      -(Complex.I * PhysicalSewing.portHalfNormalization *
          (Complex.I * PhysicalSewing.portHalfNormalization)) =
        (-Complex.I * Complex.I) *
          (PhysicalSewing.portHalfNormalization * PhysicalSewing.portHalfNormalization) := by ring
      _ = (1/2:ℂ) := by
        rw [hII, ← pow_two, PhysicalSewing.portHalfNormalization_sq]
        norm_num
  have hcenter'' : -(Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) *
      (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)))) = (1/2:ℂ) := by
    simpa only [PhysicalSewing.portHalfNormalization] using hcenter'
  have hcenterAbs : star (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) *
      (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) = (1/2:ℂ) := by
    rw [show star (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) =
        -Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) by
          simp [Complex.conj_I]]
    have halg : -Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) *
        (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) =
          -(Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) *
            (Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)))) := by ring
    rw [halg]
    exact hcenter''
  have hentry (i : Fin 3) : Tendsto
      (fun k => star (nativePhysicalAmplitude k i.val) *
        nativePhysicalAmplitude k i.val) atTop (nhds (1/2:ℂ)) := by
    have hA := nativePhysicalAmplitude_tendsto i.val
    have hstar := (continuous_star.tendsto _).comp hA
    have hprod := hstar.mul hA
    simpa only [nativePhysicalAmplitude, Function.comp_def, hcenterAbs] using hprod
  have hprod : Tendsto (fun k => ∏ i : Fin 3,
      star (nativePhysicalAmplitude k i.val) * nativePhysicalAmplitude k i.val)
      atTop (nhds (∏ _i : Fin 3, (1/2:ℂ))) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact hentry i
  have hlimit : (∏ _i : Fin 3, (1/2:ℂ)) = (1/8:ℂ) := by norm_num
  rw [← hlimit]
  change Tendsto nativePhysicalAmplitudeNormProduct atTop
    (nhds (∏ _i : Fin 3, (1/2:ℂ)))
  exact hprod

/-- The third determinant of the unchanged physical kernel has the predicted
sixth-order coefficient, transported from the existing radial dslope limit. -/
theorem nativePhysicalD3Scaled_tendsto :
    Tendsto (fun k => nativePhysicalD3 k /
      (canonicalGreenJetRealStep k : ℂ)^6) atTop
      (nhds (256 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) *
        ((hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℂ))) := by
  have hfactor : Tendsto (fun k => (8:ℂ) /
      nativePhysicalAmplitudeNormProduct k) atTop (nhds (64:ℂ)) := by
    have hquot := (tendsto_const_nhds (x := (8:ℂ))).div
      nativePhysicalAmplitudeNormProduct_tendsto
    have hquot' := hquot (by norm_num : (1/8:ℂ) ≠ 0)
    change Tendsto (fun k => (8:ℂ) /
      nativePhysicalAmplitudeNormProduct k) atTop
      (nhds ((8:ℂ) / (1/8:ℂ))) at hquot'
    have hlim : (8:ℂ) / (1/8:ℂ) = 64 := by norm_num
    rw [hlim] at hquot'
    have hlim : (8:ℂ) / (1/8:ℂ) = 64 := by norm_num
    simpa only [hlim] using hquot'
  have hds := canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto
  have hprod := hfactor.mul hds
  have hevent : ∀ᶠ k : ℕ in atTop,
      nativePhysicalD3 k / (canonicalGreenJetRealStep k : ℂ)^6 =
        ((8:ℂ) / nativePhysicalAmplitudeNormProduct k) *
          ((canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
            (canonicalGreenJetRealStep k : ℂ)^6) := by
    filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 3,
      nativePhysicalAmplitudeNormProduct_tendsto.eventually_ne
        (by norm_num : (1/8:ℂ) ≠ 0)] with k hregular hnorm
    have hdet := nativePhysicalD3_eq_scaled_dslope_det k hregular
    have heps : (canonicalGreenJetRealStep k : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      unfold canonicalGreenJetRealStep
      positivity
    rw [hdet]
    field_simp [hnorm, heps]
  have hlim : (64:ℂ) *
      ((4 * canonicalCompletedNativeLogDerivativeMoment 1 *
        (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℝ) : ℂ) =
      256 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) *
        ((hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℂ) := by
    norm_num
    ring
  have hprod' : Tendsto (fun k => ((8:ℂ) /
      nativePhysicalAmplitudeNormProduct k) *
        ((canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det /
          (canonicalGreenJetRealStep k : ℂ)^6)) atTop
      (nhds (256 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) *
        ((hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det : ℂ))) := by
    rw [hlim] at hprod
    exact hprod
  exact hprod'.congr' (hevent.mono fun k hk => hk.symm)

/-- The physical order-two Schur complement is the determinant ratio once
the physical head is nonzero. -/
theorem nativePhysicalD2_eq_head_mul_tailSchur (k : ℕ)
    (hhead : nativeRawKernel k 0 0 ≠ 0) :
    nativePhysicalD2 k = nativePhysicalD1 k *
      nativeRawSchurForm k 1 (Pi.single 1 (1 : ℂ))
        (Pi.single 1 (1 : ℂ)) := by
  rw [nativePhysicalD2, nativePhysicalD1]
  have hherm : nativeRawKernel k 1 0 = star (nativeRawKernel k 0 1) := by
    unfold nativeRawKernel
    have hc : cauchy k 1 0 = cauchy k 0 1 := by
      simp [cauchy]
    rw [hc]
    have hcs : star (cauchy k 0 1) = cauchy k 0 1 := by
      simp [cauchy]
    have hdef : 1 - star (sourceReturn k 1) * sourceReturn k 0 =
        star (1 - star (sourceReturn k 0) * sourceReturn k 1) := by
      simp
      ring
    calc
      cauchy k 0 1 * (1 - star (sourceReturn k 1) * sourceReturn k 0) =
          cauchy k 0 1 * star (1 - star (sourceReturn k 0) * sourceReturn k 1) := by
        rw [hdef]
      _ = star (cauchy k 0 1) *
          star (1 - star (sourceReturn k 0) * sourceReturn k 1) :=
        congrArg (fun a : ℂ => a * star
          (1 - star (sourceReturn k 0) * sourceReturn k 1)) hcs.symm
      _ = star (cauchy k 0 1 *
          (1 - star (sourceReturn k 0) * sourceReturn k 1)) := by simp
  have h00 : nativeRawForm k 2 (Pi.single 0 (1:ℂ)) (Pi.single 0 1) =
      nativeRawKernel k 0 0 := by
    exact (nativeBalance_eq_nativeRawForm k 2 _ _).symm.trans
      (nativeBalance_basis_eq_nativeRawKernel k 2 0 0)
  have h01 : nativeRawForm k 2 (Pi.single 0 (1:ℂ)) (Pi.single 1 1) =
      nativeRawKernel k 0 1 := by
    exact (nativeBalance_eq_nativeRawForm k 2 _ _).symm.trans
      (nativeBalance_basis_eq_nativeRawKernel k 2 0 1)
  have h11 : nativeRawForm k 2 (Pi.single 1 (1:ℂ)) (Pi.single 1 1) =
      nativeRawKernel k 1 1 := by
    exact (nativeBalance_eq_nativeRawForm k 2 _ _).symm.trans
      (nativeBalance_basis_eq_nativeRawKernel k 2 1 1)
  simp only [nativePhysicalCauchyMatrix, Matrix.of_apply,
    Matrix.det_fin_two]
  norm_num
  rw [nativeRawSchurForm]
  simp only [nativeRawHead]
  rw [h11, h01, h00, hherm]
  field_simp [hhead]

private def nativePhysicalTailSchur (k : ℕ) : ℂ :=
  nativeRawSchurForm k 1 (Pi.single 1 (1 : ℂ))
    (Pi.single 1 (1 : ℂ))

private def nativePhysicalTailSchurScaled (k : ℕ) : ℂ :=
  nativePhysicalTailSchur k / (canonicalGreenJetStep k)^2

/-- The first physical principal determinant is the unchanged head entry. -/
theorem nativePhysicalD1_tendsto :
    Tendsto nativePhysicalD1 atTop
      (nhds (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  change Tendsto (fun k => nativeRawKernel k 0 0) atTop
    (nhds (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)))
  exact nativeRawKernel_tendsto 0 0

/-- The original head entry is the first anchor deficit times its native
mass, so its eventual nonvanishing is exactly the existing low-order gate. -/
theorem nativePhysicalD1_eq_deficit_mass (k : ℕ) :
    nativePhysicalD1 k = (oneDeficit k : ℂ) * (anchorMass k : ℂ) := by
  have hform := nativeRawForm_headHead_eq k 0
  have hentry : nativeRawForm k 1 (Pi.single 0 (1:ℂ))
      (Pi.single 0 (1:ℂ)) = nativeRawKernel k 0 0 := by
    exact (nativeBalance_eq_nativeRawForm k 1 _ _).symm.trans
      (nativeBalance_basis_eq_nativeRawKernel k 1 0 0)
  rw [nativePhysicalD1]
  calc
    nativeRawKernel k 0 0 = nativeRawForm k 1
        (Pi.single 0 (1:ℂ)) (Pi.single 0 (1:ℂ)) := hentry.symm
    _ = nativeRawForm k 1 (nativeRawHead 0) (nativeRawHead 0) := by
      rfl
    _ = (oneDeficit k : ℂ) * (anchorMass k : ℂ) := hform

/-- The existing first odd native jet fixes the normalization of the
one-dimensional physical tail Schur pivot. -/
theorem nativePhysicalTailSchurScaled_tendsto :
    Tendsto nativePhysicalTailSchurScaled atTop
      (nhds (4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
  let jetSchur := fun k : ℕ => nativeRawSchurForm k 1
    (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)
    (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)
  let amplitude := fun k : ℕ => nativeFirstOddJetTailScale k *
    canonicalGreenJetStep k
  have hj : Tendsto jetSchur atTop
      (nhds (2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
    simpa only [jetSchur] using nativeRawJetSchur_firstOdd_tendsto
  have ha := nativeFirstOddJetTailScale_absSq_mul_greenStep_sq_tendsto
  have hratio : Tendsto (fun k => jetSchur k /
      (star (amplitude k) * amplitude k)) atTop
      (nhds (4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
    have hden : Tendsto (fun k => star (amplitude k) * amplitude k)
        atTop (nhds (1/2:ℂ)) := by simpa only [amplitude] using ha
    have hquot := hj.div hden
    have hlim : (2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) /
        (1/2:ℂ) = 4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
      field_simp
      ring
    have hquot' := hquot (by norm_num : (1/2:ℂ) ≠ 0)
    change Tendsto (fun k => jetSchur k /
      (star (amplitude k) * amplitude k)) atTop
      (nhds ((2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) /
        (1/2:ℂ))) at hquot'
    rw [hlim] at hquot'
    exact hquot'
  have hexact : ∀ᶠ k : ℕ in atTop,
      jetSchur k = star (nativeFirstOddJetTailScale k) *
        nativeFirstOddJetTailScale k * nativePhysicalTailSchur k := by
    simpa only [jetSchur, nativePhysicalTailSchur] using
      nativeRawJetSchur_firstOdd_exact_scale
  have hidentity : ∀ᶠ k : ℕ in atTop,
      jetSchur k / (star (amplitude k) * amplitude k) =
        nativePhysicalTailSchurScaled k := by
    have hg : ∀ᶠ k : ℕ in atTop,
        star (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) *
          (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) ≠ 0 :=
      ha.eventually_ne (by norm_num : (1/2:ℂ) ≠ 0)
    filter_upwards [hexact, hg] with k hk hg
    have heps : canonicalGreenJetStep k ≠ 0 := by
      unfold canonicalGreenJetStep
      apply inv_ne_zero
      exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
    have hstar : star (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) =
        star (nativeFirstOddJetTailScale k) * canonicalGreenJetStep k := by
      simp [canonicalGreenJetStep]
    have hfactor : star (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) *
        (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) =
          (star (nativeFirstOddJetTailScale k) * nativeFirstOddJetTailScale k) *
            (canonicalGreenJetStep k)^2 := by
      rw [hstar]
      ring
    have hk' : nativeRawSchurForm k 1
        (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)
        (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection) =
        star (nativeFirstOddJetTailScale k) * nativeFirstOddJetTailScale k *
          nativeRawSchurForm k 1 (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) := by
      simpa only [jetSchur, nativePhysicalTailSchur] using hk
    have hscale : star (nativeFirstOddJetTailScale k) *
        nativeFirstOddJetTailScale k ≠ 0 := by
      intro hz
      apply hg
      rw [hfactor, hz]
      simp
    have hscaleStar : star (nativeFirstOddJetTailScale k) ≠ 0 :=
      (mul_ne_zero_iff.mp hscale).1
    have hscale' : nativeFirstOddJetTailScale k ≠ 0 :=
      (mul_ne_zero_iff.mp hscale).2
    dsimp only [jetSchur, amplitude, nativePhysicalTailSchurScaled,
      nativePhysicalTailSchur]
    rw [hk', hfactor]
    field_simp [heps, hscaleStar, hscale']
  exact hratio.congr' hidentity

/-- The two-source determinant has its predicted `K⁻²` scale, derived from
the physical first Schur pivot and the already-proved first odd source jet. -/
theorem nativePhysicalD2Scaled_tendsto :
    Tendsto (fun k => nativePhysicalD2 k / (canonicalGreenJetStep k)^2)
      atTop (nhds (16 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
  have htail := nativePhysicalTailSchurScaled_tendsto
  have hprod := nativePhysicalD1_tendsto.mul htail
  have hevent : ∀ᶠ k : ℕ in atTop,
      nativePhysicalD2 k / (canonicalGreenJetStep k)^2 =
        nativePhysicalD1 k * nativePhysicalTailSchurScaled k := by
    filter_upwards [oneDeficit_eventually_pos] with k hk
    have hhead : nativeRawKernel k 0 0 ≠ 0 := by
      change nativePhysicalD1 k ≠ 0
      rw [nativePhysicalD1_eq_deficit_mass]
      exact mul_ne_zero (by exact_mod_cast (ne_of_gt hk))
        (by exact_mod_cast (anchorMass_pos k).ne')
    have hdet := nativePhysicalD2_eq_head_mul_tailSchur k hhead
    have heps : canonicalGreenJetStep k ≠ 0 := by
      unfold canonicalGreenJetStep
      apply inv_ne_zero
      exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
    rw [hdet]
    dsimp only [nativePhysicalTailSchurScaled, nativePhysicalTailSchur]
    field_simp [heps]
  have hlim : (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) *
      (4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) =
        16 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
          (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by ring
  have hprod' : Tendsto (fun k => nativePhysicalD1 k *
      nativePhysicalTailSchurScaled k) atTop
      (nhds (16 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
    simpa only [hlim] using hprod
  exact hprod'.congr' (hevent.mono fun k hk => hk.symm)

/-- The two-source determinant with the real radial step in the denominator.
This is the normalization used by the determinant-ratio calculation below. -/
theorem nativePhysicalD2RealStepScaled_tendsto :
    Tendsto (fun k => nativePhysicalD2 k /
      (canonicalGreenJetRealStep k : ℂ)^2) atTop
      (nhds (16 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
  simpa only [canonicalGreenJetRealStep_coe] using
    nativePhysicalD2Scaled_tendsto

private def nativePhysicalSecondSchurPivotScaled (k : ℕ) : ℂ :=
  nativePhysicalSecondSchurPivot k /
    (canonicalGreenJetRealStep k : ℂ)^4

/-- The main three-source result: the second physical Schur pivot, multiplied
by the fourth inverse mesh scale, converges to the canonical second Hankel
Schur complement.  The quotient is formed from the determinants of the
unchanged raw Cauchy kernel; the proof only uses their independently derived
physical asymptotics. -/
theorem nativePhysicalSecondSchurPivotScaled_tendsto :
    Tendsto nativePhysicalSecondSchurPivotScaled atTop
      (nhds (16 * (((canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 /
          canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℝ) : ℂ))) := by
  let m := canonicalCompletedNativeLogDerivativeMoment
  have hlow :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hm0 : 0 < m 0 := hlow.1
  have hm1 : 0 < m 1 := hlow.2
  have hm0ne : (m 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm0.ne'
  have hm1ne : (m 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm1.ne'
  have hdetReal : (hankelGram m 2).det = m 0 * m 2 - (m 1)^2 := by
    simp [hankelGram, Matrix.det_fin_two]
    ring
  have hnum := nativePhysicalD3Scaled_tendsto
  have hden := nativePhysicalD2RealStepScaled_tendsto
  have hdenLimitNe :
      (16 * (m 0 : ℂ) * (m 1 : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm0ne) hm1ne
  have hratio := hnum.div hden
  have hratio' := hratio hdenLimitNe
  have hlimit :
      (256 * (m 1 : ℂ) * ((hankelGram m 2).det : ℂ)) /
          (16 * (m 0 : ℂ) * (m 1 : ℂ)) =
        (16 * (m 2 - m 1^2 / m 0) : ℝ) := by
    rw [hdetReal]
    push_cast
    field_simp [hm0.ne', hm1.ne']
    ring
  rw [hlimit] at hratio'
  have hcast :
      ((16 * (m 2 - m 1^2 / m 0) : ℝ) : ℂ) =
        16 * ((m 2 - m 1^2 / m 0 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_mul]
  rw [hcast] at hratio'
  have hmesh (k : ℕ) : (canonicalGreenJetRealStep k : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold canonicalGreenJetRealStep
    positivity
  have hdetEventuallyNe : ∀ᶠ k : ℕ in atTop, nativePhysicalD2 k ≠ 0 := by
    filter_upwards [hden.eventually_ne hdenLimitNe] with k hk
    have hquot : nativePhysicalD2 k /
        (canonicalGreenJetRealStep k : ℂ)^2 ≠ 0 := by simpa only using hk
    exact (div_ne_zero_iff.mp hquot).1
  have hratioIdentity : ∀ᶠ k : ℕ in atTop,
      (nativePhysicalD3 k / (canonicalGreenJetRealStep k : ℂ)^6) /
          (nativePhysicalD2 k / (canonicalGreenJetRealStep k : ℂ)^2) =
        nativePhysicalSecondSchurPivotScaled k := by
    filter_upwards [hdetEventuallyNe] with k hk
    have heps := hmesh k
    dsimp [nativePhysicalSecondSchurPivotScaled,
      nativePhysicalSecondSchurPivot]
    field_simp [hk, heps]
  exact hratio'.congr' hratioIdentity

private theorem complex_tendsto_eventually_re_pos
    {f : ℕ → ℂ} {z : ℂ}
    (h : Tendsto f atTop (nhds z)) (hz : 0 < z.re) :
    ∀ᶠ k : ℕ in atTop, 0 < (f k).re := by
  have hre : Tendsto (fun k => (f k).re) atTop (nhds z.re) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp h
  apply Filter.Tendsto.eventually_lt tendsto_const_nhds hre
  simpa only [Complex.ofReal_re] using hz

/-- The physical two-source determinant is eventually positive on its
`(k+1)⁻²` scale. -/
theorem nativePhysicalD2_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalD2 k).re := by
  let m := canonicalCompletedNativeLogDerivativeMoment
  have hlow :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hlim : 0 <
      (16 * (m 0 : ℂ) * (m 1 : ℂ)).re := by
    simp
    exact mul_pos (mul_pos (by norm_num) hlow.1) hlow.2
  have hscaled := complex_tendsto_eventually_re_pos
    nativePhysicalD2RealStepScaled_tendsto hlim
  filter_upwards [hscaled] with k hk
  have heps : 0 < canonicalGreenJetRealStep k ^ 2 := by
    unfold canonicalGreenJetRealStep
    positivity
  have hk' : 0 < (nativePhysicalD2 k).re /
      canonicalGreenJetRealStep k ^ 2 := by
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hk
  exact (div_pos_iff_of_pos_right heps).mp hk'

/-- The physical three-source determinant is eventually positive on its
`(k+1)⁻⁶` scale, using the independent second Hankel determinant sign. -/
theorem nativePhysicalD3_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalD3 k).re := by
  let m := canonicalCompletedNativeLogDerivativeMoment
  have hlow :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hdet := canonicalCompletedNativeHankel_two_det_pos
  have hlim : 0 <
      (256 * (m 1 : ℂ) * ((hankelGram m 2).det : ℂ)).re := by
    simp
    exact mul_pos (mul_pos (by norm_num) hlow.2) hdet
  have hscaled := complex_tendsto_eventually_re_pos
    nativePhysicalD3Scaled_tendsto hlim
  filter_upwards [hscaled] with k hk
  have heps : 0 < canonicalGreenJetRealStep k ^ 6 := by
    unfold canonicalGreenJetRealStep
    positivity
  have hk' : 0 < (nativePhysicalD3 k).re /
      canonicalGreenJetRealStep k ^ 6 := by
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hk
  exact (div_pos_iff_of_pos_right heps).mp hk'

/-- The leading physical pivot is eventually positive, from its raw kernel
limit and the independent sign of `h₀`. -/
theorem nativePhysicalP0_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalP0 k).re := by
  have h0 : 0 < canonicalCompletedNativeLogDerivativeMoment 0 :=
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).1
  have hlim : 0 <
      (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)).re := by
    simp
    positivity
  have h := complex_tendsto_eventually_re_pos nativePhysicalD1_tendsto hlim
  simpa only [nativePhysicalP0] using h

/-- The first deflated physical pivot is eventually positive by the D₂ and
D₁ scales. -/
theorem nativePhysicalP1_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalP1 k).re := by
  let m := canonicalCompletedNativeLogDerivativeMoment
  have hlow :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hD1 := nativePhysicalP0_eventually_re_pos
  have hD2scaled : ∀ᶠ k : ℕ in atTop,
      0 < (nativePhysicalD2 k /
        (canonicalGreenJetRealStep k : ℂ)^2).re := by
    apply complex_tendsto_eventually_re_pos nativePhysicalD2RealStepScaled_tendsto
    simp
    exact mul_pos (mul_pos (by norm_num) hlow.1) hlow.2
  have hD2 : ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalD2 k).re := by
    filter_upwards [hD2scaled] with k hk
    have heps : 0 < canonicalGreenJetRealStep k ^ 2 := by
      unfold canonicalGreenJetRealStep
      positivity
    have hk' : 0 < (nativePhysicalD2 k).re /
        canonicalGreenJetRealStep k ^ 2 := by
      simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hk
    exact (div_pos_iff_of_pos_right heps).mp hk'
  filter_upwards [hD1, hD2] with k h1 h2
  have h1cast : nativePhysicalD1 k = (nativePhysicalD1 k).re := by
    have him := congrArg Complex.im (nativePhysicalD1_star k)
    have him' : -(nativePhysicalD1 k).im = (nativePhysicalD1 k).im := by
      simpa using him
    have himzero : (nativePhysicalD1 k).im = 0 := by linarith
    apply Complex.ext
    · rfl
    · simpa using himzero
  have h2cast : nativePhysicalD2 k = (nativePhysicalD2 k).re := by
    have him := congrArg Complex.im (nativePhysicalD2_star k)
    have him' : -(nativePhysicalD2 k).im = (nativePhysicalD2 k).im := by
      simpa using him
    have himzero : (nativePhysicalD2 k).im = 0 := by linarith
    apply Complex.ext
    · rfl
    · simpa using himzero
  have hquot : (nativePhysicalD2 k / nativePhysicalD1 k).re =
      (nativePhysicalD2 k).re / (nativePhysicalD1 k).re := by
    rw [h1cast, h2cast]
    simp
  rw [nativePhysicalP1, hquot]
  exact div_pos h2 h1

/-- The second physical Schur pivot is eventually positive. Its limit is
proved first; only here is the independent canonical second-Schur sign used. -/
theorem nativePhysicalP2_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (nativePhysicalSecondSchurPivot k).re := by
  let m := canonicalCompletedNativeLogDerivativeMoment
  have hdelta := canonicalCompletedNativeSecondSchurComplement_pos
  have hlow :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hlimitPos : 0 <
      (16 * ((m 2 - m 1^2 / m 0 : ℝ) : ℂ)).re := by
    have hreal :
        (16 * ((m 2 - m 1^2 / m 0 : ℝ) : ℂ)).re =
          16 * (m 2 - m 1^2 / m 0) := by
      rw [show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
    rw [hreal]
    exact mul_pos (by norm_num) hdelta
  have hscaledPos := complex_tendsto_eventually_re_pos
    nativePhysicalSecondSchurPivotScaled_tendsto hlimitPos
  have hD2ne : ∀ᶠ k : ℕ in atTop, nativePhysicalD2 k ≠ 0 :=
    (nativePhysicalD2RealStepScaled_tendsto.eventually_ne (by
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr hlow.1.ne'))
          (Complex.ofReal_ne_zero.mpr hlow.2.ne'))).mono fun k hk => by
      have heps : (canonicalGreenJetRealStep k : ℂ)^2 ≠ 0 := by
        exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by
          unfold canonicalGreenJetRealStep
          positivity))
      exact (div_ne_zero_iff.mp hk).1
  filter_upwards [hscaledPos, hD2ne] with k hscaled hD2
  have hD3real : star (nativePhysicalD3 k) = nativePhysicalD3 k :=
    nativePhysicalD3_star k
  have hD2real : star (nativePhysicalD2 k) = nativePhysicalD2 k :=
    nativePhysicalD2_star k
  have hpivotReal : star (nativePhysicalSecondSchurPivot k) =
      nativePhysicalSecondSchurPivot k := by
    simp [nativePhysicalSecondSchurPivot, hD3real, hD2real]
  have himD2 : (nativePhysicalD2 k).im = 0 := by
    have him := congrArg Complex.im hD2real
    have h' : -(nativePhysicalD2 k).im = (nativePhysicalD2 k).im := by simpa using him
    linarith
  have himD3 : (nativePhysicalD3 k).im = 0 := by
    have him := congrArg Complex.im hD3real
    have h' : -(nativePhysicalD3 k).im = (nativePhysicalD3 k).im := by simpa using him
    linarith
  have hpivotCast : nativePhysicalSecondSchurPivot k =
      (nativePhysicalSecondSchurPivot k).re := by
    apply Complex.ext
    · rfl
    · have him := congrArg Complex.im hpivotReal
      have h' : -(nativePhysicalSecondSchurPivot k).im =
          (nativePhysicalSecondSchurPivot k).im := by simpa using him
      have himzero : (nativePhysicalSecondSchurPivot k).im = 0 := by linarith
      simpa using himzero
  have heps : 0 < canonicalGreenJetRealStep k ^ 4 := by
    unfold canonicalGreenJetRealStep
    positivity
  have hscaleRe : (nativePhysicalSecondSchurPivotScaled k).re =
      (nativePhysicalSecondSchurPivot k).re /
        canonicalGreenJetRealStep k ^ 4 := by
    simp only [nativePhysicalSecondSchurPivotScaled,
      ← Complex.ofReal_pow, Complex.div_ofReal_re]
  have hpivot : 0 < (nativePhysicalSecondSchurPivot k).re := by
    rw [hscaleRe] at hscaled
    exact (div_pos_iff_of_pos_right heps).mp hscaled
  exact hpivot

theorem nativePhysicalP2_eventually_re_pos' :
    ∀ᶠ k : ℕ in atTop, 0 < (nativePhysicalP2 k).re := by
  simpa [nativePhysicalP2, nativePhysicalSecondSchurPivot] using
    nativePhysicalP2_eventually_re_pos

private def nativePhysicalThreePointTopRight (k : ℕ) :
    Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.of fun i _ => nativeRawKernel k i.val 2

private def nativePhysicalThreePointBottomRight (k : ℕ) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of fun _ _ => nativeRawKernel k 2 2

/-- Reindexing the unchanged three-source matrix by its first two sources
and its final source exposes its exact Hermitian block form. -/
theorem nativePhysicalCauchyMatrix_three_reindex_eq_fromBlocks (k : ℕ) :
    (nativePhysicalCauchyMatrix k 3).submatrix
        nativePhysicalFinThreeBlockEquiv nativePhysicalFinThreeBlockEquiv =
      Matrix.fromBlocks (nativePhysicalCauchyMatrix k 2)
        (nativePhysicalThreePointTopRight k)
        (Matrix.conjTranspose (nativePhysicalThreePointTopRight k))
        (nativePhysicalThreePointBottomRight k) := by
  classical
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [nativePhysicalFinThreeBlockEquiv,
            nativePhysicalCauchyMatrix, Matrix.fromBlocks]
      | inr j =>
          simp [nativePhysicalFinThreeBlockEquiv,
            nativePhysicalCauchyMatrix, nativePhysicalThreePointTopRight,
            Matrix.fromBlocks]
  | inr i =>
      cases j with
      | inl j =>
          simp [nativePhysicalFinThreeBlockEquiv,
            nativePhysicalCauchyMatrix, nativePhysicalThreePointTopRight,
            Matrix.fromBlocks, nativeRawKernel_hermitian_entry]
      | inr j =>
          simp [nativePhysicalFinThreeBlockEquiv,
            nativePhysicalCauchyMatrix,
            nativePhysicalThreePointBottomRight, Matrix.fromBlocks]

/-- The original three-source Cauchy matrix is eventually positive definite.
Its leading two-source block comes from the existing low-order Pick gate, and
its final scalar Schur complement is the positive second physical pivot. -/
theorem nativePhysicalCauchyMatrix_three_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (nativePhysicalCauchyMatrix k 3).PosDef := by
  filter_upwards [
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef,
    nativePhysicalD2_eventually_re_pos,
    nativePhysicalP2_eventually_re_pos',
    nativePhysicalD3_eventually_re_pos] with k hPick hD2 hP2 hD3
  let A : Matrix (Fin 2) (Fin 2) ℂ := nativePhysicalCauchyMatrix k 2
  let B := nativePhysicalThreePointTopRight k
  let D := nativePhysicalThreePointBottomRight k
  let M := nativePhysicalCauchyMatrix k 3
  have hAsem : A.PosSemidef := by
    change (nativePhysicalCauchyMatrix k 2).PosSemidef
    rw [nativePhysicalCauchyMatrix_eq_nativePick]
    exact hPick
  have hA_det : A.det = nativePhysicalD2 k := by
    simp [A, nativePhysicalD2]
  have hD2ne : nativePhysicalD2 k ≠ 0 := by
    intro hzero
    have hpos : 0 < (nativePhysicalD2 k).re := hD2
    simp [hzero] at hpos
  have hA_det_ne : A.det ≠ 0 := by
    rw [hA_det]
    exact hD2ne
  have hApos : A.PosDef := hAsem.posDef_iff_det_ne_zero.mpr hA_det_ne
  letI : Invertible A := hApos.isUnit.invertible
  let S : Matrix (Fin 1) (Fin 1) ℂ :=
    D - Matrix.conjTranspose B * A⁻¹ * B
  have hblock :
      (M.submatrix nativePhysicalFinThreeBlockEquiv
          nativePhysicalFinThreeBlockEquiv) =
        Matrix.fromBlocks A B (Matrix.conjTranspose B) D := by
    simpa [A, B, D] using
      nativePhysicalCauchyMatrix_three_reindex_eq_fromBlocks k
  have hdetBlock :
      (Matrix.fromBlocks A B (Matrix.conjTranspose B) D).det = A.det * S.det := by
    simpa [S] using Matrix.det_fromBlocks₁₁ A B (Matrix.conjTranspose B) D
  have hdetReindexed : (M.submatrix nativePhysicalFinThreeBlockEquiv
      nativePhysicalFinThreeBlockEquiv).det = nativePhysicalD3 k := by
    rw [Matrix.det_submatrix_equiv_self]
    simp [M, nativePhysicalD3]
  have hdetBlock_eq :
      (Matrix.fromBlocks A B (Matrix.conjTranspose B) D).det =
        nativePhysicalD3 k := by
    rw [← hblock, hdetReindexed]
  have hmul : A.det * S.det = nativePhysicalD3 k := by
    calc
      A.det * S.det =
          (Matrix.fromBlocks A B (Matrix.conjTranspose B) D).det := hdetBlock.symm
      _ = nativePhysicalD3 k := hdetBlock_eq
  have hSdet : S.det = nativePhysicalSecondSchurPivot k := by
    dsimp [nativePhysicalSecondSchurPivot]
    calc
      S.det = (A.det * S.det) / A.det := by field_simp [hA_det_ne]
      _ = nativePhysicalD3 k / A.det := by rw [hmul]
      _ = nativePhysicalD3 k / nativePhysicalD2 k := by rw [hA_det]
  have hSdetEntry : S.det = S 0 0 := by simp [S]
  have hSentry : S 0 0 = nativePhysicalSecondSchurPivot k := by
    rw [← hSdetEntry]
    exact hSdet
  have hPivot : 0 < (nativePhysicalSecondSchurPivot k).re := by
    simpa [nativePhysicalP2, nativePhysicalSecondSchurPivot] using hP2
  have hPivotReal : star (nativePhysicalSecondSchurPivot k) =
      nativePhysicalSecondSchurPivot k := by
    simp [nativePhysicalSecondSchurPivot,
      nativePhysicalD2_star, nativePhysicalD3_star]
  have hPivotEqRe : nativePhysicalSecondSchurPivot k =
      (nativePhysicalSecondSchurPivot k).re := by
    apply Complex.ext
    · rfl
    · have him := congrArg Complex.im hPivotReal
      have hneg : -(nativePhysicalSecondSchurPivot k).im =
          (nativePhysicalSecondSchurPivot k).im := by simpa using him
      have himzero : (nativePhysicalSecondSchurPivot k).im = 0 := by linarith
      simpa using himzero
  have hSdiag : S = Matrix.diagonal
      (fun _ : Fin 1 => ((nativePhysicalSecondSchurPivot k).re : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.diagonal, hSentry, ← hPivotEqRe]
  have hSpos : S.PosSemidef := by
    rw [hSdiag]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact RCLike.ofReal_nonneg.mpr (le_of_lt hPivot)
  have hBlocksPos :
      (Matrix.fromBlocks A B (Matrix.conjTranspose B) D).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hApos).mpr
      (by simpa [S] using hSpos)
  have hMsem : M.PosSemidef := by
    apply (Matrix.posSemidef_submatrix_equiv
      nativePhysicalFinThreeBlockEquiv).mp
    rw [hblock]
    exact hBlocksPos
  have hD3ne : nativePhysicalD3 k ≠ 0 := by
    intro hzero
    have hpos : 0 < (nativePhysicalD3 k).re := hD3
    simp [hzero] at hpos
  have hMdet : M.det = nativePhysicalD3 k := by
    simp [M, nativePhysicalD3]
  exact hMsem.posDef_iff_det_ne_zero.mpr (by rw [hMdet]; exact hD3ne)

end
end CarryCauchyResidual
