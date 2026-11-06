import SigmaFiniteRationalIntervalBoxes

/-!
# Conditional exact-rational propagation for C5 finite minors

The coefficient-box hypotheses are explicit. This module does not prove the
analytic inclusion of the original source coefficients in those boxes.
-/

namespace CarrySigmaObstruction

open CarrySigmaSource CarrySigmaPade
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sigmaRatBallSub (a b : SigmaRatBall) : SigmaRatBall :=
  a + sigmaRatBallNeg b

def sigmaRatBallScale (q : ℚ) (a : SigmaRatBall) : SigmaRatBall :=
  sigmaRatBallMul (sigmaRatBallConst q) a

def sigmaRatBallSum {α : Type} [DecidableEq α] (s : Finset α)
    (f : α → SigmaRatBall) : SigmaRatBall := ∑ i ∈ s, f i

theorem sigmaRatBallContains_sum {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → SigmaRatBall) (g : α → ℝ)
    (hfg : ∀ i ∈ s, sigmaRatBallContains (f i) (g i)) :
    sigmaRatBallContains (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sigmaRatBallContains]
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      apply sigmaRatBallContains_add
      · exact hfg i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hfg j (Finset.mem_insert_of_mem hj)

theorem sigmaRatBallContains_const (q : ℚ) :
    sigmaRatBallContains (sigmaRatBallConst q) (q : ℝ) := by
  simp [sigmaRatBallContains, sigmaRatBallConst]

theorem sigmaRatBallConst_nat (n : ℕ) :
    sigmaRatBallContains (sigmaRatBallConst n) (n : ℝ) := by
  exact sigmaRatBallContains_const n

theorem sigmaRatBallScale_valid {q : ℚ} {a : SigmaRatBall}
    (ha : sigmaRatBallValid a) : sigmaRatBallValid (sigmaRatBallScale q a) := by
  exact sigmaRatBallMul_valid (sigmaRatBallConst_valid q) ha

theorem sigmaRatBallScale_contains {q : ℚ} {a : SigmaRatBall} {x : ℝ}
    (ha : sigmaRatBallValid (sigmaRatBallConst q))
    (ha' : sigmaRatBallValid a)
    (hx : sigmaRatBallContains (sigmaRatBallConst q) (q : ℝ))
    (hxa : sigmaRatBallContains a x) :
    sigmaRatBallContains (sigmaRatBallScale q a) ((q : ℝ) * x) := by
  exact sigmaRatBallContains_mul ha ha' hx hxa

def sigmaFiniteScaledMomentBall (c : ℕ → SigmaRatBall) : ℕ → SigmaRatBall
  | 0 => sigmaRatBallNeg
      (sigmaRatBallMul (sigmaRatBallConst 1)
        (sigmaRatBallMul (c 1) (sigmaRatBallPow (c 0) 0)))
  | n + 1 => sigmaRatBallNeg
      (sigmaRatBallMul (sigmaRatBallConst (n + 2))
          (sigmaRatBallMul (c (n + 2)) (sigmaRatBallPow (c 0) (n + 1))) +
        ∑ j ∈ Finset.range (n + 1),
          sigmaRatBallMul
            (sigmaRatBallMul (c (j + 1))
              (sigmaFiniteScaledMomentBall c (n + 1 - (j + 1))))
            (sigmaRatBallPow (c 0) j))
termination_by n => n
decreasing_by omega

def sigmaFiniteScaledMomentBallMinor (c : ℕ → SigmaRatBall) (s : ℕ) : SigmaRatBall :=
  sigmaRatBallSub
    (sigmaRatBallMul (sigmaFiniteScaledMomentBall c s)
      (sigmaFiniteScaledMomentBall c (s + 2)))
    (sigmaRatBallMul (sigmaFiniteScaledMomentBall c (s + 1))
      (sigmaFiniteScaledMomentBall c (s + 1)))

def sigmaRatBallLower (b : SigmaRatBall) : ℚ := b.1 - b.2

def sigmaRatBallUpper (b : SigmaRatBall) : ℚ := b.1 + b.2

theorem sigmaRatBallValid_sum {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → SigmaRatBall)
    (hf : ∀ i ∈ s, sigmaRatBallValid (f i)) :
    sigmaRatBallValid (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sigmaRatBallValid]
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact sigmaRatBallAdd_valid (hf i (Finset.mem_insert_self i s)) <| by
        apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

theorem sigmaFiniteScaledMomentBall_eq_recurrence (c : ℕ → SigmaRatBall) (n : ℕ) :
    sigmaFiniteScaledMomentBall c n = sigmaRatBallNeg
      (sigmaRatBallMul (sigmaRatBallConst (n + 1))
          (sigmaRatBallMul (c (n + 1)) (sigmaRatBallPow (c 0) n)) +
        ∑ j ∈ Finset.range n,
          sigmaRatBallMul
            (sigmaRatBallMul (c (j + 1))
              (sigmaFiniteScaledMomentBall c (n - (j + 1))))
            (sigmaRatBallPow (c 0) j)) := by
  cases n with
  | zero =>
      simp [sigmaFiniteScaledMomentBall, sigmaRatBallConst, sigmaRatBallPow,
        sigmaRatBallMul, sigmaRatBallNeg]
  | succ n =>
      simp only [sigmaFiniteScaledMomentBall]
      have hindex : n + 2 = n + 1 + 1 := by omega
      rw [hindex]
      have hcast : (n : ℚ) + 2 = (n : ℚ) + 1 + 1 := by ring
      rw [hcast]
      have hcast' : ((n + 1 : ℕ) : ℚ) + 1 = (n : ℚ) + 1 + 1 := by
        norm_num [Nat.cast_add]
      rw [hcast']

theorem sigmaFiniteScaledMomentBall_valid_bounded (c : ℕ → SigmaRatBall)
    (N : ℕ) (hc : ∀ i ≤ N, sigmaRatBallValid (c i)) :
    ∀ n, n + 1 ≤ N → sigmaRatBallValid (sigmaFiniteScaledMomentBall c n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [sigmaFiniteScaledMomentBall_eq_recurrence]
      apply sigmaRatBallNeg_valid
      apply sigmaRatBallAdd_valid
      · apply sigmaRatBallMul_valid
        · exact sigmaRatBallConst_valid _
        · apply sigmaRatBallMul_valid
          · exact hc (n + 1) (by omega)
          · exact sigmaRatBallPow_valid (hc 0 (by omega)) n
      · apply sigmaRatBallValid_sum
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have hprev_lt : n - (j + 1) < n := by omega
        have hprev_bound : n - (j + 1) + 1 ≤ N := by omega
        apply sigmaRatBallMul_valid
        · apply sigmaRatBallMul_valid
          · exact hc (j + 1) (by omega)
          · exact ih (n - (j + 1)) hprev_lt hprev_bound
        · exact sigmaRatBallPow_valid (hc 0 (by omega)) j

theorem sigmaFiniteScaledMomentBall_contains_of_recurrence
    (cBox : ℕ → SigmaRatBall) (cReal : ℕ → ℝ) (pReal : ℕ → ℝ) (N : ℕ)
    (hcValid : ∀ i ≤ N, sigmaRatBallValid (cBox i))
    (hcContains : ∀ i ≤ N, sigmaRatBallContains (cBox i) (cReal i))
    (hpRec : ∀ n, n + 1 ≤ N →
      pReal n = -((n + 1 : ℝ) * cReal (n + 1) * cReal 0 ^ n) -
        ∑ j ∈ Finset.range n,
          cReal (j + 1) * pReal (n - (j + 1)) * cReal 0 ^ j) :
    ∀ n, n + 1 ≤ N →
      sigmaRatBallContains (sigmaFiniteScaledMomentBall cBox n) (pReal n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hzeroValid := hcValid 0 (by omega)
      have hzeroContains := hcContains 0 (by omega)
      have hpowValid := sigmaRatBallPow_valid hzeroValid
      have hpowContains := sigmaRatBallContains_pow hzeroValid hzeroContains
      have hcoefValid := hcValid (n + 1) (by omega)
      have hcoefContains := hcContains (n + 1) (by omega)
      have hconstValid := sigmaRatBallConst_valid (n + 1 : ℚ)
      have hconstContains : sigmaRatBallContains
          (sigmaRatBallConst ((n : ℚ) + 1)) ((n : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using sigmaRatBallConst_nat (n + 1)
      have hleadInnerValid := sigmaRatBallMul_valid hcoefValid (hpowValid n)
      have hleadInnerContains := sigmaRatBallContains_mul
        hcoefValid (hpowValid n) hcoefContains (hpowContains n)
      have hleadValid := sigmaRatBallMul_valid hconstValid hleadInnerValid
      have hleadContains := sigmaRatBallContains_mul
        hconstValid hleadInnerValid hconstContains hleadInnerContains
      have htermContains : ∀ j ∈ Finset.range n,
          sigmaRatBallContains
            (sigmaRatBallMul
              (sigmaRatBallMul (cBox (j + 1))
                (sigmaFiniteScaledMomentBall cBox (n - (j + 1))))
              (sigmaRatBallPow (cBox 0) j))
            (cReal (j + 1) * pReal (n - (j + 1)) * cReal 0 ^ j) := by
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have hprevBound : n - (j + 1) + 1 ≤ N := by omega
        have hprevValid := sigmaFiniteScaledMomentBall_valid_bounded
          cBox N hcValid (n - (j + 1)) hprevBound
        have hprevContains := ih (n - (j + 1)) (by omega) hprevBound
        have hcoefValid' := hcValid (j + 1) (by omega)
        have hcoefContains' := hcContains (j + 1) (by omega)
        have hpowValid' := hpowValid j
        have hpowContains' := hpowContains j
        have hmulValid := sigmaRatBallMul_valid hcoefValid' hprevValid
        have hmulContains := sigmaRatBallContains_mul
          hcoefValid' hprevValid hcoefContains' hprevContains
        have hterm := sigmaRatBallContains_mul hmulValid hpowValid' hmulContains hpowContains'
        simpa [mul_assoc] using hterm
      have htailContains := sigmaRatBallContains_sum (Finset.range n)
        (fun j => sigmaRatBallMul
          (sigmaRatBallMul (cBox (j + 1))
            (sigmaFiniteScaledMomentBall cBox (n - (j + 1))))
          (sigmaRatBallPow (cBox 0) j))
        (fun j => cReal (j + 1) * pReal (n - (j + 1)) * cReal 0 ^ j)
        htermContains
      have hsumContains := sigmaRatBallContains_add hleadContains htailContains
      have hnegContains := sigmaRatBallContains_neg hsumContains
      rw [sigmaFiniteScaledMomentBall_eq_recurrence, hpRec n hn]
      convert hnegContains using 1
      ring

theorem sigmaFiniteScaledMomentBallMinor_contains
    (cBox : ℕ → SigmaRatBall) (pReal : ℕ → ℝ) (N s : ℕ)
    (hs : s + 3 ≤ N)
    (hcValid : ∀ i ≤ N, sigmaRatBallValid (cBox i))
    (hpS : sigmaRatBallContains (sigmaFiniteScaledMomentBall cBox s) (pReal s))
    (hpS1 : sigmaRatBallContains (sigmaFiniteScaledMomentBall cBox (s + 1))
      (pReal (s + 1)))
    (hpS2 : sigmaRatBallContains (sigmaFiniteScaledMomentBall cBox (s + 2))
      (pReal (s + 2))) :
    sigmaRatBallContains (sigmaFiniteScaledMomentBallMinor cBox s)
      (pReal s * pReal (s + 2) - (pReal (s + 1)) ^ 2) := by
  have hpSValid := sigmaFiniteScaledMomentBall_valid_bounded cBox N hcValid s (by omega)
  have hpS1Valid := sigmaFiniteScaledMomentBall_valid_bounded cBox N hcValid (s + 1) (by omega)
  have hpS2Valid := sigmaFiniteScaledMomentBall_valid_bounded cBox N hcValid (s + 2) (by omega)
  have hprod := sigmaRatBallContains_mul hpSValid hpS2Valid hpS hpS2
  have hsquare := sigmaRatBallContains_mul hpS1Valid hpS1Valid hpS1 hpS1
  have hneg := sigmaRatBallContains_neg hsquare
  have hminor := sigmaRatBallContains_add hprod hneg
  simpa [sigmaFiniteScaledMomentBallMinor, sigmaRatBallSub, pow_two, sub_eq_add_neg] using hminor

theorem sigmaRatBallContains_pos_of_lower {b : SigmaRatBall} {x : ℝ}
    (hlower : 0 < sigmaRatBallLower b)
    (hcontains : sigmaRatBallContains b x) : 0 < x := by
  change |x - (b.1 : ℝ)| ≤ (b.2 : ℝ) at hcontains
  rcases abs_le.mp hcontains with ⟨hlo, hhi⟩
  have hlowerR : 0 < (b.1 : ℝ) - (b.2 : ℝ) := by
    exact_mod_cast hlower
  linarith

theorem sigmaRatBallContains_neg_of_upper {b : SigmaRatBall} {x : ℝ}
    (hupper : sigmaRatBallUpper b < 0)
    (hcontains : sigmaRatBallContains b x) : x < 0 := by
  change |x - (b.1 : ℝ)| ≤ (b.2 : ℝ) at hcontains
  rcases abs_le.mp hcontains with ⟨hlo, hhi⟩
  have hupperR : (b.1 : ℝ) + (b.2 : ℝ) < 0 := by
    exact_mod_cast hupper
  linarith

def sigmaC00495SourceBoxes : Prop :=
  ∀ n, n < 15 → sigmaRatBallContains (sigmaC00495CoefficientBall n)
    (completedSigmaDisplacedSourceCoefficient (99 / 2000) n)

def sigmaC01SourceBoxes : Prop :=
  ∀ n, n < 13 → sigmaRatBallContains (sigmaC01CoefficientBall n)
    (completedSigmaDisplacedSourceCoefficient (1 / 10) n)

end
end CarrySigmaObstruction
