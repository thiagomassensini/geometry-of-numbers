import GeometryOfNumbers.Analysis.RealDiscreteValveSeries
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Canonical triangular tower integration and channel extraction

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.TowerValve

variable {R : Type*} [CommRing R]

def IsTowerChannel (a b : ℕ → R) : Prop :=
  ∀ n, ∑ i ∈ Finset.range (n + 1), b i * a (n - i) = (n : R) * a n

theorem tower_channel_unique (a b₁ b₂ : ℕ → R) (ha : a 0 = 1)
    (h₁ : IsTowerChannel a b₁) (h₂ : IsTowerChannel a b₂) : b₁ = b₂ := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hdist : ∑ i ∈ Finset.range (n + 1), (b₁ i - b₂ i) * a (n - i)
        = (∑ i ∈ Finset.range (n + 1), b₁ i * a (n - i))
          - ∑ i ∈ Finset.range (n + 1), b₂ i * a (n - i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => sub_mul (b₁ i) (b₂ i) (a (n - i))
    have hsum : ∑ i ∈ Finset.range (n + 1), (b₁ i - b₂ i) * a (n - i) = 0 := by
      rw [hdist, h₁ n, h₂ n, sub_self]
    rw [Finset.sum_range_succ] at hsum
    have hzero : ∑ i ∈ Finset.range n, (b₁ i - b₂ i) * a (n - i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [ih i (Finset.mem_range.mp hi), sub_self, zero_mul]
    rw [hzero, zero_add, Nat.sub_self, ha, mul_one, sub_eq_zero] at hsum
    exact hsum

def IsLogDerivChannel (A B : PowerSeries R) : Prop :=
  B * A = PowerSeries.X * A.derivativeFun

theorem isLogDerivChannel_mul {A₁ A₂ B₁ B₂ : PowerSeries R}
    (h₁ : IsLogDerivChannel A₁ B₁) (h₂ : IsLogDerivChannel A₂ B₂) :
    IsLogDerivChannel (A₁ * A₂) (B₁ + B₂) := by
  unfold IsLogDerivChannel at h₁ h₂ ⊢
  rw [PowerSeries.derivativeFun_mul]
  linear_combination h₁ * A₂ + h₂ * A₁

theorem isTowerChannel_iff_isLogDerivChannel (a b : ℕ → R) :
    IsTowerChannel a b ↔ IsLogDerivChannel (PowerSeries.mk a) (PowerSeries.mk b) := by
  have hlhs : ∀ n, (PowerSeries.coeff n) (PowerSeries.mk b * PowerSeries.mk a)
      = ∑ i ∈ Finset.range (n + 1), b i * a (n - i) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
  have hrhs : ∀ n, (PowerSeries.coeff n)
      (PowerSeries.X * (PowerSeries.mk a).derivativeFun) = (n : R) * a n := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
        PowerSeries.coeff_mk]
      push_cast
      ring
  unfold IsTowerChannel IsLogDerivChannel
  rw [PowerSeries.ext_iff]
  exact forall_congr' fun n => by rw [hlhs, hrhs]

section Reconstruction

variable {K : Type*} [Field K] [CharZero K]

noncomputable def towerMass (b : ℕ → K) : ℕ → K
  | 0 => 1
  | (n + 1) => (↑(n + 1) : K)⁻¹ *
      ∑ i ∈ (Finset.range (n + 1)).attach, b (i.1 + 1) * towerMass b (n - i.1)
  decreasing_by
    have := Finset.mem_range.mp i.2
    omega

omit [CharZero K] in
@[simp] theorem towerMass_zero (b : ℕ → K) : towerMass b 0 = 1 := by
  rw [towerMass]

theorem isTowerChannel_towerMass (b : ℕ → K) (hb : b 0 = 0) :
    IsTowerChannel (towerMass b) b := by
  intro n
  cases n with
  | zero => simp [hb]
  | succ m =>
    have hm : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hrhs : ((m + 1 : ℕ) : K) * towerMass b (m + 1)
        = ∑ i ∈ Finset.range (m + 1), b (i + 1) * towerMass b (m - i) := by
      rw [towerMass, ← mul_assoc, mul_inv_cancel₀ hm, one_mul,
        Finset.sum_attach (Finset.range (m + 1))
          (fun i => b (i + 1) * towerMass b (m - i))]
    rw [hrhs, Finset.sum_range_succ', hb, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.succ_sub_succ]

theorem towerMass_unique (a a' b : ℕ → K) (ha : a 0 = 1) (ha' : a' 0 = 1)
    (h : IsTowerChannel a b) (h' : IsTowerChannel a' b) : a = a' := by
  have hb0 : b 0 = 0 := by
    have h0 := h 0
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, ha, mul_one,
      Nat.cast_zero] at h0
    exact h0
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [ha, ha']
    · have hn : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have ea := h (m + 1)
      have ea' := h' (m + 1)
      rw [Finset.sum_range_succ'] at ea ea'
      simp only [hb0, zero_mul, add_zero, Nat.sub_zero] at ea ea'
      have hsum : ∑ i ∈ Finset.range (m + 1), b (i + 1) * a (m + 1 - (i + 1))
          = ∑ i ∈ Finset.range (m + 1), b (i + 1) * a' (m + 1 - (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hlt : m + 1 - (i + 1) < m + 1 := by
          have := Finset.mem_range.mp hi; omega
        rw [ih _ hlt]
      rw [hsum] at ea
      exact mul_left_cancel₀ hn (ea.symm.trans ea')

theorem towerMass_eq_of_isTowerChannel (a b : ℕ → K) (ha : a 0 = 1)
    (h : IsTowerChannel a b) : towerMass b = a := by
  have hb0 : b 0 = 0 := by
    have h0 := h 0
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, ha, mul_one,
      Nat.cast_zero] at h0
    exact h0
  exact towerMass_unique (towerMass b) a b (towerMass_zero b) ha
    (isTowerChannel_towerMass b hb0) h

end Reconstruction

section Exp

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def expSeries (K : PowerSeries A) : PowerSeries A := (exp A).subst K

theorem isLogDerivChannel_expSeries (K : PowerSeries A) (hK : constantCoeff K = 0) :
    IsLogDerivChannel (expSeries K) (X * K.derivativeFun) := by
  have hsub : HasSubst K := HasSubst.of_constantCoeff_zero' hK
  have d_eq : ∀ f : PowerSeries A, d⁄dX A f = f.derivativeFun := fun _ => rfl
  have hchain : (expSeries K).derivativeFun = expSeries K * K.derivativeFun := by
    rw [← d_eq, ← d_eq]
    show d⁄dX A ((exp A).subst K) = (exp A).subst K * d⁄dX A K
    rw [derivative_subst (hg := hsub), derivative_exp A]
  unfold IsLogDerivChannel
  rw [hchain]; ring

theorem constantCoeff_expSeries (K : PowerSeries A) (hK : constantCoeff K = 0) :
    constantCoeff (expSeries K) = 1 := by
  have hsub : HasSubst K := HasSubst.of_constantCoeff_zero' hK
  rw [← coeff_zero_eq_constantCoeff_apply, expSeries, coeff_subst' hsub,
    finsum_eq_single _ 0 fun d hd => by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, hK, zero_pow hd, smul_zero]]
  simp

end Exp

section ExpTowerMass

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

noncomputable def logIntegral (b : ℕ → K) : PowerSeries K :=
  mk fun n => if n = 0 then 0 else b n / n

omit [CharZero K] in
theorem constantCoeff_logIntegral (b : ℕ → K) :
    constantCoeff (logIntegral b) = 0 := by
  rw [logIntegral, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]; simp

theorem X_mul_derivativeFun_logIntegral (b : ℕ → K) (hb : b 0 = 0) :
    X * (logIntegral b).derivativeFun = mk b := by
  ext n
  cases n with
  | zero => simp [hb]
  | succ m =>
    have hm : (m : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [coeff_succ_X_mul, coeff_derivativeFun, logIntegral, coeff_mk, coeff_mk,
      if_neg (Nat.succ_ne_zero m)]
    push_cast
    field_simp

theorem mk_towerMass_eq_expSeries (b : ℕ → K) (hb : b 0 = 0) :
    mk (towerMass b) = expSeries (logIntegral b) := by
  have hc : constantCoeff (logIntegral b) = 0 := constantCoeff_logIntegral b
  have h1 : IsLogDerivChannel (expSeries (logIntegral b)) (mk b) := by
    have h := isLogDerivChannel_expSeries (logIntegral b) hc
    rwa [X_mul_derivativeFun_logIntegral b hb] at h
  set A := expSeries (logIntegral b) with hA
  have hmk : mk (fun n => coeff n A) = A := by ext n; rw [coeff_mk]
  have hTower : IsTowerChannel (fun n => coeff n A) b :=
    (isTowerChannel_iff_isLogDerivChannel (fun n => coeff n A) b).mpr (by rw [hmk]; exact h1)
  have ha0 : (fun n => coeff n A) 0 = 1 := by
    show coeff 0 A = 1
    rw [hA, coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_expSeries (logIntegral b) hc
  have huniq := towerMass_unique (towerMass b) (fun n => coeff n A) b
    (towerMass_zero b) ha0 (isTowerChannel_towerMass b hb) hTower
  rw [huniq]; exact hmk

end ExpTowerMass

end GeometryOfNumbers.Analysis.TowerValve

namespace GeometryOfNumbers.Analysis.TowerValve

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def canonicalTowerChannel (a : ℕ → R) : ℕ → R :=
  Nat.lt_wfRel.wf.fix fun n previous =>
    (n : R) * a n -
      ∑ i : Fin n, previous i i.isLt * a (n - i)

theorem canonicalTowerChannel_eq (a : ℕ → R) (n : ℕ) :
    canonicalTowerChannel a n =
      (n : R) * a n -
        ∑ i ∈ Finset.range n,
          canonicalTowerChannel a i * a (n - i) := by
  rw [canonicalTowerChannel, WellFounded.fix_eq]
  refine congrArg (fun s : R => (n : R) * a n - s) ?_
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]

@[simp] theorem canonicalTowerChannel_zero (a : ℕ → R) :
    canonicalTowerChannel a 0 = 0 := by
  rw [canonicalTowerChannel_eq]
  simp

theorem canonicalTowerChannel_isTowerChannel
    (a : ℕ → R) (ha : a 0 = 1) :
    IsTowerChannel a (canonicalTowerChannel a) := by
  intro n
  rw [Finset.sum_range_succ, Nat.sub_self, ha, mul_one,
    canonicalTowerChannel_eq a n]
  ring

theorem canonicalTowerChannel_eq_of_isTowerChannel
    (a b : ℕ → R) (ha : a 0 = 1)
    (hb : IsTowerChannel a b) :
    canonicalTowerChannel a = b :=
  tower_channel_unique a (canonicalTowerChannel a) b ha
    (canonicalTowerChannel_isTowerChannel a ha) hb

theorem existsUnique_towerChannel
    (a : ℕ → R) (ha : a 0 = 1) :
    ∃! b : ℕ → R, IsTowerChannel a b := by
  refine ⟨canonicalTowerChannel a,
    canonicalTowerChannel_isTowerChannel a ha, ?_⟩
  intro b hb
  exact (canonicalTowerChannel_eq_of_isTowerChannel a b ha hb).symm

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

theorem towerMass_canonicalTowerChannel
    (a : ℕ → K) (ha : a 0 = 1) :
    towerMass (canonicalTowerChannel a) = a :=
  towerMass_eq_of_isTowerChannel a (canonicalTowerChannel a) ha
    (canonicalTowerChannel_isTowerChannel a ha)

theorem canonicalTowerChannel_towerMass
    (b : ℕ → K) (hb : b 0 = 0) :
    canonicalTowerChannel (towerMass b) = b :=
  canonicalTowerChannel_eq_of_isTowerChannel (towerMass b) b
    (towerMass_zero b) (isTowerChannel_towerMass b hb)

theorem mk_eq_expSeries_logIntegral_canonicalTowerChannel
    (a : ℕ → K) (ha : a 0 = 1) :
    PowerSeries.mk a =
      expSeries (logIntegral (canonicalTowerChannel a)) := by
  calc
    PowerSeries.mk a =
        PowerSeries.mk (towerMass (canonicalTowerChannel a)) :=
      congrArg (fun f : ℕ → K => PowerSeries.mk f)
        (towerMass_canonicalTowerChannel a ha).symm
    _ = expSeries (logIntegral (canonicalTowerChannel a)) :=
      mk_towerMass_eq_expSeries (canonicalTowerChannel a)
        (canonicalTowerChannel_zero a)

end CharacteristicZero

end GeometryOfNumbers.Analysis.TowerValve
