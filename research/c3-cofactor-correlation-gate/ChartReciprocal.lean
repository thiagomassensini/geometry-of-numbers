import CorrelationGate

namespace C3CofactorCorrelation

open CarryC3Boxes CarryC3Tail CarryC3Gamma C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

def chartJetBoxTable : Fin 13 → Box := ![
  ⟨-366025403784438646763723170753 / 500000000000000000000000000000, -146410161513775458705489268301 / 200000000000000000000000000000⟩,
  ⟨1902852301792691931559163317633 / 1000000000000000000000000000000, 951426150896345965779581658817 / 500000000000000000000000000000⟩,
  ⟨-65328028820932807772837477533 / 62500000000000000000000000000, -1045248461134924924365399640527 / 1000000000000000000000000000000⟩,
  ⟨191387134019043262444251387217 / 500000000000000000000000000000, 76554853607617304977700554887 / 200000000000000000000000000000⟩,
  ⟨-52565064331572838292836731069 / 500000000000000000000000000000, -105130128663145676585673462137 / 1000000000000000000000000000000⟩,
  ⟨5774862562929565542428571697 / 250000000000000000000000000000, 23099450251718262169714286789 / 1000000000000000000000000000000⟩,
  ⟨-4229556651335890418788160827 / 1000000000000000000000000000000, -2114778325667945209394080413 / 500000000000000000000000000000⟩,
  ⟨663806130396506945509266879 / 1000000000000000000000000000000, 2074394157489084204716459 / 3125000000000000000000000000⟩,
  ⟨-91158196518353518942413649 / 1000000000000000000000000000000, -5697387282397094933900853 / 62500000000000000000000000000⟩,
  ⟨11127501656431740886911187 / 1000000000000000000000000000000, 2781875414107935221727797 / 250000000000000000000000000000⟩,
  ⟨-611240503096532823463567 / 500000000000000000000000000000, -1222481006193065646927133 / 1000000000000000000000000000000⟩,
  ⟨12209387782427794798991 / 100000000000000000000000000000, 122093877824277947989911 / 1000000000000000000000000000000⟩,
  ⟨-2794454886435303362991 / 250000000000000000000000000000, -11177819545741213451963 / 1000000000000000000000000000000⟩
]

def normalizedChartReciprocalBoxTable : Fin 13 → Box := ![
  ⟨1 / 1, 1 / 1⟩,
  ⟨2599344583898510502872449514197 / 1000000000000000000000000000000, 81229518246828453214764047319 / 31250000000000000000000000000⟩,
  ⟨5328756314665621761062002129959 / 1000000000000000000000000000000, 1332189078666405440265500532503 / 250000000000000000000000000000⟩,
  ⟨426508623724353625714333645187 / 40000000000000000000000000000, 10662715593108840642858341129873 / 1000000000000000000000000000000⟩,
  ⟨21323015427982340609471122405241 / 1000000000000000000000000000000, 21323015427982340609471122405921 / 1000000000000000000000000000000⟩,
  ⟨8529162844410809147749794689159 / 200000000000000000000000000000, 42645814222054045738748973448037 / 1000000000000000000000000000000⟩,
  ⟨42645845233396779080247680026371 / 500000000000000000000000000000, 85291690466793558160495360059971 / 1000000000000000000000000000000⟩,
  ⟨170583389268770145351032304034551 / 1000000000000000000000000000000, 10661461829298134084439519003597 / 62500000000000000000000000000⟩,
  ⟨10661461779277804514372972206673 / 31250000000000000000000000000, 170583388468444872229967555343079 / 500000000000000000000000000000⟩,
  ⟨5330730887291928020224896559231 / 7812500000000000000000000000, 341166776786683393294393379904879 / 500000000000000000000000000000⟩,
  ⟨136466710718599154439986199597317 / 100000000000000000000000000000, 682333553592995772199930998344017 / 500000000000000000000000000000⟩,
  ⟨1364667107191139851441386173366121 / 500000000000000000000000000000, 2729334214382279702882772348967509 / 1000000000000000000000000000000⟩,
  ⟨2729334214381841026811680003122463 / 500000000000000000000000000000, 1091733685752736410724672002645171 / 200000000000000000000000000000⟩
]

/-- A sum of boxes with outward rounding after each addition. -/
def roundedSumBoxFin {N : ℕ} (a : Fin N → Box) : Box :=
  bsum (fun j => if hj : j < N then a ⟨j, hj⟩ else Box.point 0) N

theorem rounded_sum_box_fin_contains {N : ℕ} (a : Fin N → Box) (f : Fin N → ℝ)
    (h : ∀ j, (a j).Contains (f j)) :
    (roundedSumBoxFin a).Contains (∑ j : Fin N, f j) := by
  let a' : ℕ → Box := fun j => if hj : j < N then a ⟨j, hj⟩ else Box.point 0
  let f' : ℕ → ℝ := fun j => if hj : j < N then f ⟨j, hj⟩ else 0
  have hs := bsum_contains N a' f' (by
      intro j hj
      simp [a', f', hj]
      exact h ⟨j, hj⟩)
  have he : (∑ j : Fin N, f j) =
      ∑ j ∈ Finset.range N, f' j := by
    simpa [f'] using Fin.sum_univ_eq_sum_range f' N
  rw [he]
  simpa [roundedSumBoxFin, a'] using hs

/-- One outward-rounded interval step for the normalized chart reciprocal. At
orders below 13 it uses the already certified preceding table entries, so the
verifier never re-expands the full reciprocal recurrence tree. -/
def normalizedChartReciprocalBoxCalc (r : ℕ) : Box :=
  if hr : r < 13 then
    if hz : r = 0 then Box.point 1
    else
      bmul (bneg (roundedSumBoxFin (fun j : Fin r =>
        bmul (normalizedChartReciprocalBoxTable ⟨j.val, by omega⟩)
          (chartJetBoxTable ⟨r-j.val, by omega⟩))))
        (binv (chartJetBoxTable 0))
  else (chartJetBoxExact 0).mul (reciprocalJetBoxExact chartJetBoxExact r)

def normalizedChartReciprocalBox (r : ℕ) : Box :=
  if hr : r < 13 then normalizedChartReciprocalBoxTable ⟨r, hr⟩
  else normalizedChartReciprocalBoxCalc r

theorem chartScale_eq_chartRealJet_zero : chartScale = chartRealJet 0 := by
  norm_num [chartScale, chartRealJet]

theorem chart_jet_box_table_bound (r : Fin 13) :
    (chartJetBoxExact r.val).Subset (chartJetBoxTable r) := by
  fin_cases r <;> norm_num [chartJetBoxExact, chartJetBoxTable, powBoxExact,
    Box.mul, Box.inv, Box.neg, Box.sub, Box.add, Box.point, Box.Subset,
    chartAmplitudeReferenceTight, logThreeBoxTight, logReferenceTight]

theorem chart_jet_box_table_contains (r : Fin 13) :
    (chartJetBoxTable r).Contains (chartRealJet r.val) :=
  Box.subset_contains (chart_jet_box_table_bound r) (chart_jet_box_exact r.val)

theorem normalized_chart_reciprocal_box_table_bound (r : Fin 13) :
    (normalizedChartReciprocalBoxCalc r.val).Subset
      (normalizedChartReciprocalBoxTable r) := by
  fin_cases r <;> decide +kernel

theorem normalized_chart_reciprocal_table_contains (n : ℕ) (hn : n < 13) :
    (normalizedChartReciprocalBoxTable ⟨n, hn⟩).Contains
      (chartScale * reciprocalJet chartRealJet n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hscale : chartScale * (chartRealJet 0)⁻¹ = 1 := by
        rw [← chartScale_eq_chartRealJet_zero]
        exact mul_inv_cancel₀ chartScale_ne_zero
      rw [reciprocalJet, hscale]
      norm_num [normalizedChartReciprocalBoxTable, Box.point, Box.Contains]
    | succ n =>
      have hsum : (roundedSumBoxFin (fun j : Fin (n+1) =>
          bmul (normalizedChartReciprocalBoxTable ⟨j.val, by omega⟩)
            (chartJetBoxTable ⟨n+1-j.val, by omega⟩))).Contains
          (∑ j : Fin (n+1),
            (chartScale * reciprocalJet chartRealJet j.val) *
              chartRealJet (n+1-j.val)) := by
        apply rounded_sum_box_fin_contains
        intro j
        exact bmul_contains
          (ih j.val (by omega) (by omega))
          (chart_jet_box_table_contains ⟨n+1-j.val, by omega⟩)
      have hinv : (binv (chartJetBoxTable 0)).Contains
          (chartRealJet 0)⁻¹ :=
        binv_contains (chart_jet_box_table_contains 0)
          (Or.inr (by norm_num [chartJetBoxTable]))
      have hstep := bmul_contains (Box.neg_contains hsum) hinv
      have hrec : chartScale * reciprocalJet chartRealJet (n+1) =
          -(∑ j : Fin (n+1),
            (chartScale * reciprocalJet chartRealJet j.val) *
              chartRealJet (n+1-j.val)) * (chartRealJet 0)⁻¹ := by
        have hsumScale :
            (∑ j : Fin (n+1),
              (chartScale * reciprocalJet chartRealJet j.val) *
                chartRealJet (n+1-j.val)) =
              chartScale * (∑ j : Fin (n+1),
                reciprocalJet chartRealJet j.val * chartRealJet (n+1-j.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [reciprocalJet, div_eq_mul_inv,
          show chartRealJet 0 = chartScale from chartScale_eq_chartRealJet_zero.symm,
          hsumScale]
        field_simp [chartScale_ne_zero]
      rw [← hrec] at hstep
      have hstep' : (normalizedChartReciprocalBoxCalc (n+1)).Contains
          (chartScale * reciprocalJet chartRealJet (n+1)) := by
        simpa [normalizedChartReciprocalBoxCalc, hn, bneg] using hstep
      exact Box.subset_contains
        (normalized_chart_reciprocal_box_table_bound ⟨n+1, hn⟩) hstep'

def exactRangeSumBox (f : ℕ → Box) (n : ℕ) : Box :=
  sumBoxFinExact (fun j : Fin (n + 1) => f j.val)

theorem exact_range_sum_box_contains (f : ℕ → Box) (g : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n + 1, (f j).Contains (g j)) :
    (exactRangeSumBox f n).Contains (∑ j ∈ Finset.range (n + 1), g j) := by
  have hh := sumBoxFinExact_contains
    (fun j : Fin (n + 1) => f j.val)
    (fun j : Fin (n + 1) => g j.val)
    (fun j => h j.val (by omega))
  have he : (∑ j : Fin (n + 1), g j.val) =
      ∑ j ∈ Finset.range (n + 1), g j :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => g j) (n + 1)
  rw [he] at hh
  exact hh

theorem normalizedChartReciprocal_eq_scale_mul (r : ℕ) :
    normalizedChartReciprocal chartRatio (Real.log 3) r =
      chartScale * reciprocalJet chartRealJet r := by
  rw [reciprocalJet_chart_eq_normalized]
  rw [← mul_assoc, mul_inv_cancel₀ chartScale_ne_zero, one_mul]

theorem normalized_chart_reciprocal_box_contains (r : ℕ) :
    (normalizedChartReciprocalBox r).Contains
      (normalizedChartReciprocal chartRatio (Real.log 3) r) := by
  have hnorm := normalizedChartReciprocal_eq_scale_mul r
  by_cases h : r < 13
  · have ht := normalized_chart_reciprocal_table_contains r h
    rw [hnorm]
    simpa [normalizedChartReciprocalBox, h] using ht
  · have hs : (chartJetBoxExact 0).Contains chartScale := by
      rw [chartScale_eq_chartRealJet_zero]
      exact chart_jet_box_exact 0
    have hr : (reciprocalJetBoxExact chartJetBoxExact r).Contains
        (reciprocalJet chartRealJet r) :=
      reciprocal_jet_box_exact chartJetBoxExact chartRealJet chart_jet_box_exact
        (Or.inr chart_center_interval_negative_exact) r
    have hp := Box.mul_contains hs hr
    rw [hnorm]
    simpa [normalizedChartReciprocalBox, h, normalizedChartReciprocalBoxCalc] using hp


end
end C3CofactorCorrelation
