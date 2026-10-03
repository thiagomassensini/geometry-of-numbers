import GeometryOfNumbers.Analysis.FiniteClockHeightLedger

/-! Literal exact-arithmetic transcription of the finite Chebyshev loop.
This constructor is distinguished from the preexisting LDL Jacobi section.
Its determinism is proved; no equality to that section is postulated. -/

noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
open FiniteClockJets FiniteClockHeightLedger

structure ChebyshevState where
  previous : ℕ → ℝ
  current : ℕ → ℝ
  alpha : ℕ → ℝ
  beta : ℕ → ℝ

def chebyshevSeed (h : ℕ → ℝ) (d : ℕ) : ChebyshevState where
  previous := fun _ => 0
  current := fun ell => if ell < 2*d then h ell else 0
  alpha := fun k => if k = 0 then h 1 / h 0 else 0
  beta := fun k => if k = 0 then h 0 else 0

def chebyshevUpdated (d k : ℕ) (state : ChebyshevState) (ell : ℕ) : ℝ :=
  if k ≤ ell ∧ ell < 2*d-k then
    state.current (ell+1) - state.alpha (k-1) * state.current ell -
      state.beta (k-1) * state.previous ell
  else 0

def chebyshevStep (d k : ℕ) (state : ChebyshevState) : ChebyshevState where
  previous := state.current
  current := chebyshevUpdated d k state
  alpha := fun j => if j = k then
    chebyshevUpdated d k state (k+1) / chebyshevUpdated d k state k -
      state.current k / state.current (k-1) else state.alpha j
  beta := fun j => if j = k then
    chebyshevUpdated d k state k / state.current (k-1) else state.beta j

def chebyshevRun (h : ℕ → ℝ) (d : ℕ) : ℕ → ChebyshevState
  | 0 => chebyshevSeed h d
  | k+1 => chebyshevStep d (k+1) (chebyshevRun h d k)

def historicalChebyshevJacobi (h : ℕ → ℝ) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  let state := chebyshevRun h d (d-1)
  fun i j => if i = j then state.alpha i.val
    else if i.val+1 = j.val then Real.sqrt (state.beta j.val)
    else if j.val+1 = i.val then Real.sqrt (state.beta i.val) else 0

/-- Positivity of squared off-diagonals is the literal script gate.
Zero denominators are also excluded to interpret the totalized Lean divisions
as successful Python divisions. -/
def HistoricalChebyshevAdmissible (h : ℕ → ℝ) (d : ℕ) : Prop :=
  h 0 ≠ 0 ∧
  (∀ k, 1 ≤ k → k < d →
    let state := chebyshevRun h d (k-1)
    state.current (k-1) ≠ 0 ∧ chebyshevUpdated d k state k ≠ 0) ∧
  (∀ k, 1 ≤ k → k < d → 0 < (chebyshevRun h d (d-1)).beta k)

theorem historicalChebyshevJacobi_isSymm (h : ℕ → ℝ) (d : ℕ) :
    (historicalChebyshevJacobi h d).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [historicalChebyshevJacobi]
  by_cases hij : i = j
  · subst j; simp
  · simp only [hij, Ne.symm hij, if_false]
    by_cases ha : i.val+1 = j.val
    · have hb : ¬j.val+1 = i.val := by omega
      simp [ha,hb]
    · by_cases hb : j.val+1 = i.val <;> simp [ha,hb]

private theorem chebyshevSeed_congr {h h' : ℕ → ℝ} {d : ℕ} (hd : 0 < d)
    (hp : ∀ k, k < 2*d → h k = h' k) : chebyshevSeed h d = chebyshevSeed h' d := by
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  unfold chebyshevSeed
  congr 1
  · funext k
    by_cases hk : k < 2*d
    · simp [hk, hp k hk]
    · simp [hk]
  · simp only [h0,h1]
  · simp only [h0]

/-- The production loop depends only on h_0,...,h_(2d-1). -/
theorem historicalChebyshevJacobi_prefix {h h' : ℕ → ℝ} (d : ℕ)
    (hp : ∀ k, k < 2*d → h k = h' k) :
    historicalChebyshevJacobi h d = historicalChebyshevJacobi h' d := by
  by_cases hd : d = 0
  · subst d; ext i; exact Fin.elim0 i
  have hseed := chebyshevSeed_congr (by omega : 0 < d) hp
  have hr : ∀ k, chebyshevRun h d k = chebyshevRun h' d k := by
    intro k
    induction k with
    | zero => exact hseed
    | succ k ih => simp only [chebyshevRun, ih]
  simp only [historicalChebyshevJacobi, hr]

/-- Exact clock dependence of the translated historical Chebyshev constructor.
The separate tail/factor/completion data are fixed hypotheses, not clock outputs. -/
theorem finiteClockJets_determine_historicalChebyshev {M M' : ℕ}
    (w : Fin M → ℝ) (w' : Fin M' → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (d : ℕ)
    (hjets : ∀ k, k ≤ 4*d →
      finiteHeadReadout w (normalizedClockJet k (historicalInitialState M)) =
      finiteHeadReadout w' (normalizedClockJet k (historicalInitialState M'))) :
    historicalChebyshevJacobi
      (historicalScaledMoment (historicalPhi w tail cameraFactor completion)) d =
    historicalChebyshevJacobi
      (historicalScaledMoment (historicalPhi w' tail cameraFactor completion)) d := by
  apply historicalChebyshevJacobi_prefix
  intro k hk
  have hp := finiteClockJets_determine_phiPrefix w w' tail cameraFactor completion d hjets
  have hs : historicalScale (historicalPhi w tail cameraFactor completion) =
      historicalScale (historicalPhi w' tail cameraFactor completion) := by
    unfold historicalScale
    rw [finiteLogMoment_triangular 0 (fun j hj => hp j (by omega))]
  unfold historicalScaledMoment scaledMoment
  rw [hs, finiteLogMoment_triangular k (fun j hj => hp j (by omega))]

def historicalChebyshevHeight (phi : ℕ → ℝ) (d : ℕ)
    (hJ : (historicalChebyshevJacobi (historicalScaledMoment phi) d).PosDef) :
    Matrix (Fin d) (Fin d) ℝ :=
  scaledFiniteHeightOperator hJ (historicalScale phi)

/-- The exact finite spectral transform of the literal recurrence matrix,
under positivity. No spectral relationship with the material clock is claimed. -/
theorem historicalChebyshevHeight_charpoly (phi : ℕ → ℝ) (d : ℕ)
    (hJ : (historicalChebyshevJacobi (historicalScaledMoment phi) d).PosDef) :
    (historicalChebyshevHeight phi d hJ).charpoly =
      ∏ j : Fin d, (Polynomial.X - Polynomial.C
        (Real.sqrt (historicalScale phi / hJ.isHermitian.eigenvalues j))) :=
  scaledFiniteHeightOperator_charpoly hJ _

private theorem scaledFiniteHeightOperator_congr {d : ℕ}
    {J J' : Matrix (Fin d) (Fin d) ℝ} (hJ : J.PosDef) (hJ' : J'.PosDef)
    {c c' : ℝ} (he : J = J') (hc : c = c') :
    scaledFiniteHeightOperator hJ c = scaledFiniteHeightOperator hJ' c' := by
  subst J'
  subst c'
  rfl

/-- The full finite deterministic chain, RELATIVE TO fixed external germs.
This does not close the missing modern-source or analytic-tail bridges. -/
theorem finiteClockJets_determine_historicalHeight {M M' : ℕ}
    (w : Fin M → ℝ) (w' : Fin M' → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (d : ℕ) (hd : 0 < d)
    (hjets : ∀ k, k ≤ 4*d →
      finiteHeadReadout w (normalizedClockJet k (historicalInitialState M)) =
      finiteHeadReadout w' (normalizedClockJet k (historicalInitialState M')))
    (hJ : (historicalChebyshevJacobi (historicalScaledMoment
      (historicalPhi w tail cameraFactor completion)) d).PosDef)
    (hJ' : (historicalChebyshevJacobi (historicalScaledMoment
      (historicalPhi w' tail cameraFactor completion)) d).PosDef) :
    historicalChebyshevHeight (historicalPhi w tail cameraFactor completion) d hJ =
      historicalChebyshevHeight (historicalPhi w' tail cameraFactor completion) d hJ' := by
  apply scaledFiniteHeightOperator_congr
  · exact finiteClockJets_determine_historicalChebyshev w w' tail cameraFactor completion d hjets
  · unfold historicalScale
    apply congrArg Inv.inv
    exact finiteLogMoment_triangular 0
      (fun k hk => finiteClockJets_determine_phiPrefix w w' tail cameraFactor completion
        d hjets k (by omega))

end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
