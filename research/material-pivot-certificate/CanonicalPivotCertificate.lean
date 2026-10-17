import CanonicalComparison
import CarrySelfAdjointOperator.CompletedNativeThetaCubicQuadrature

namespace CarryMaterialThetaCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact exponential enclosure used by the rational certificate. -/
def theta_certificate_exp_lower (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)^1024

def theta_certificate_exp_upper (x : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)+
    (x/1024)^40*41/(Nat.factorial 40*40))^1024

theorem theta_certificate_exp_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1024) :
    theta_certificate_exp_lower x ≤ exp x ∧ exp x ≤ theta_certificate_exp_upper x := by
  have hy : 0 ≤ x/1024 := by positivity
  have hy1 : x/1024 ≤ 1 := by linarith
  have hl := Real.sum_le_exp_of_nonneg hy 40
  have hu := Real.exp_bound' hy hy1 (n := 40) (by norm_num)
  have hu' : exp (x/1024) ≤ (∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)+
      (x/1024)^40*41/(Nat.factorial 40*40) := by
    convert hu using 1
    norm_num
  have he : exp x = (exp (x/1024))^1024 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  constructor
  · apply pow_le_pow_left₀ _ hl
    exact Finset.sum_nonneg (fun i _ => by positivity)
  · exact pow_le_pow_left₀ (exp_nonneg _) hu' 1024

/-- The omitted fourth and later modes of the original theta source.
No finite-mode replacement of the source is made. -/
theorem theta_mode_after_three_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    XiThetaCosine.thetaTailMode (n+3) u ≤
      exp (-48)*(exp (-24))^n*exp (-95*u) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hs : (16+8*(n:ℝ)) ≤ (((n+4:ℕ):ℝ)^2) := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    nlinarith [sq_nonneg (n:ℝ)]
  have he : 1+2*u ≤ exp (2*u) := by linarith [Real.add_one_le_exp (2*u)]
  have hp : (3:ℝ)*(16+8*(n:ℝ))*(1+2*u) ≤
      Real.pi*(((n+4:ℕ):ℝ)^2)*exp (2*u) := by
    gcongr
    exact Real.pi_gt_three.le
  have hbound : 48+24*(n:ℝ)+96*u ≤
      Real.pi*(((n+4:ℕ):ℝ)^2)*exp (2*u) := by
    nlinarith [mul_nonneg hn hu]
  unfold XiThetaCosine.thetaTailMode
  rw [← exp_nat_mul,← exp_add,← exp_add,← exp_add]
  apply exp_le_exp.mpr
  have heq : n+3+1=n+4 := by omega
  rw [heq]
  nlinarith

private theorem exp48_lower : (400000000000000000000:ℝ) < exp 48 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 48) 90
  have hr : (400000000000000000000:ℝ) < ∑ i ∈ Finset.range 90,
      (48:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact hr.trans_le he

/-- Fully kernel-checked pointwise bound for the infinite omitted modes. -/
theorem theta_tail_after_three_le {u : ℝ} (hu : 0 ≤ u) :
    2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+3) u) ≤
      (1/100000000000000000000:ℝ)*exp (-95*u) := by
  have hg0 : 0 ≤ exp (-24:ℝ) := (exp_pos _).le
  have hg1 : exp (-24:ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have hsum := ((summable_nat_add_iff 3).2 (XiThetaCosine.summable_thetaTailMode u)).tsum_le_tsum
    (theta_mode_after_three_le hu)
    (((summable_geometric_of_lt_one hg0 hg1).mul_left (exp (-48:ℝ))).mul_right (exp (-95*u)))
  rw [tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one hg0 hg1] at hsum
  have h24 : exp (-24:ℝ) ≤ 1/2 := by
    rw [exp_neg]
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    linarith [Real.add_one_le_exp (24:ℝ)]
  have hinv : 1/(1-exp (-24:ℝ)) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-exp (-24:ℝ))).mpr
    linarith
  have h48 : 4*exp (-48:ℝ) ≤ (1/100000000000000000000:ℝ) := by
    rw [exp_neg]
    apply (mul_inv_le_iff₀ (exp_pos _)).mpr
    linarith [exp48_lower]
  calc
    _ ≤ 2*(exp (-48:ℝ)*(1/(1-exp (-24:ℝ)))*exp (-95*u)) :=
      by simpa only [one_div] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 2)
    _ ≤ (4*exp (-48:ℝ))*exp (-95*u) := by
      have hh := mul_le_mul_of_nonneg_left hinv (exp_pos (-48:ℝ)).le
      nlinarith [mul_nonneg (exp_pos (-95*u)).le (show 0 ≤ 2*exp (-48:ℝ)-exp (-48:ℝ)*(1/(1-exp (-24:ℝ))) by linarith)]
    _ ≤ _ := mul_le_mul_of_nonneg_right h48 (exp_pos _).le

/-- Literal source = the retained three modes + the bounded infinite tail. -/
theorem theta_three_mode_split (u : ℝ) :
    XiThetaCosine.thetaTail u =
      2*(∑ n ∈ Finset.range 3, XiThetaCosine.thetaTailMode n u)+
      2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+3) u) := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have he := Summable.sum_add_tsum_nat_add 3 (XiThetaCosine.summable_thetaTailMode u)
  rw [← he]
  ring

end
end CarryMaterialThetaCertificate

namespace CarryMaterialThetaCertificate
#assert_central_comparison_axioms theta_certificate_exp_lower
#print axioms theta_certificate_exp_lower
#assert_central_comparison_axioms theta_certificate_exp_upper
#print axioms theta_certificate_exp_upper
#assert_central_comparison_axioms theta_certificate_exp_bounds
#print axioms theta_certificate_exp_bounds
#assert_central_comparison_axioms theta_mode_after_three_le
#print axioms theta_mode_after_three_le
#assert_central_comparison_axioms theta_tail_after_three_le
#print axioms theta_tail_after_three_le
#assert_central_comparison_axioms theta_three_mode_split
#print axioms theta_three_mode_split
end CarryMaterialThetaCertificate

-- BEGIN GENERATED MATERIAL PIVOT CERTIFICATE

namespace CarryMaterialPivotCertificate
noncomputable section
set_option autoImplicit false

theorem enclose_add {x y a b c d L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : L ≤ a+c) (hu : b+d ≤ U) : L ≤ x+y ∧ x+y ≤ U := by
  constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2,hl,hu]

theorem enclose_neg {x a b : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    -b ≤ -x ∧ -x ≤ -a := by constructor <;> linarith only [hx.1,hx.2]

theorem enclose_mul {x y a b c d L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hll : L ≤ a*c) (hlr : L ≤ a*d) (hrl : L ≤ b*c) (hrr : L ≤ b*d)
    (ull : a*c ≤ U) (ulr : a*d ≤ U) (url : b*c ≤ U) (urr : b*d ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  have hbound (z : ℝ) (hl : L ≤ z*c) (hr : L ≤ z*d)
      (ul : z*c ≤ U) (ur : z*d ≤ U) : L ≤ z*y ∧ z*y ≤ U := by
    rcases le_total 0 z with hz | hz
    · have h1 := mul_le_mul_of_nonneg_left hy.1 hz
      have h2 := mul_le_mul_of_nonneg_left hy.2 hz
      exact ⟨hl.trans h1,h2.trans ur⟩
    · have h1 := mul_le_mul_of_nonpos_left hy.2 hz
      have h2 := mul_le_mul_of_nonpos_left hy.1 hz
      exact ⟨hr.trans h1,h2.trans ul⟩
  have ha := hbound a hll hlr ull ulr
  have hb := hbound b hrl hrr url urr
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hy0),
      (mul_le_mul_of_nonpos_right hx.1 hy0).trans ha.2⟩

theorem enclose_inv {x a b L U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : 0 < a) (hl : L ≤ 1/b) (hu : 1/a ≤ U) :
    L ≤ 1/x ∧ 1/x ≤ U := by
  have hx0 : 0 < x := ha.trans_le hx.1
  exact ⟨hl.trans (one_div_le_one_div_of_le hx0 hx.2),
    (one_div_le_one_div_of_le ha hx.1).trans hu⟩
end
end CarryMaterialPivotCertificate

namespace CarryMaterialPivotCertificate
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarryMaterialSourceFactorComparison CarryMaterialFourthPivotComparison
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
local notation "h" => canonicalCompletedNativeLogDerivativeMoment
local notation "c" => completedNativeRealEvenCharacteristicCoefficient

def material_fourth_theta_box_lower : Fin 10 → ℝ := ![(115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ),(247320713366732650218889654413503763/1000000000000000000000000000000000000000:ℝ),(4000101370527710015207524445255511/200000000000000000000000000000000000000:ℝ),(5754071852616085966370295496664877/2000000000000000000000000000000000000000:ℝ),(1474373230547965236999548382721929/2500000000000000000000000000000000000000:ℝ),(776040428721882815494537188678519/5000000000000000000000000000000000000000:ℝ),(123521074954908160410478039005927/2500000000000000000000000000000000000000:ℝ),(45783634487247840546360071464651/2500000000000000000000000000000000000000:ℝ),(3079455788683529239640494208701/400000000000000000000000000000000000000:ℝ),(36011790549172927647565520455659/10000000000000000000000000000000000000000:ℝ)]

def material_fourth_theta_box_upper : Fin 10 → ℝ := ![(57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ),(2473207133667326502607677522105484947/10000000000000000000000000000000000000000:ℝ),(100002534263192750482411997556849461/5000000000000000000000000000000000000000:ℝ),(5754071852616085991398122174464751/2000000000000000000000000000000000000000:ℝ),(5897492922191861033942937309299143/10000000000000000000000000000000000000000:ℝ),(1552080857443765695263706301153963/10000000000000000000000000000000000000000:ℝ),(98816859963926538641550737088273/2000000000000000000000000000000000000000:ℝ),(7325381517959656245580136266111/400000000000000000000000000000000000000:ℝ),(9623299339636033816206051328717/1250000000000000000000000000000000000000:ℝ),(7202358109834593002361801435879/2000000000000000000000000000000000000000:ℝ)]

/-- Analytic input still requiring a kernel-checked quadrature bridge. The
Python certificate supplies it as a rigorous computation, not a Lean axiom. -/
def material_fourth_theta_box : Prop := ∀ k : Fin 10,
  material_fourth_theta_box_lower k ≤ completedNativeThetaTailMoment (2*k) ∧
  completedNativeThetaTailMoment (2*k) ≤ material_fourth_theta_box_upper k

private theorem characteristic_enclosures (hb : material_fourth_theta_box) :
    ((9942415563766282198254462057135953080063/20000000000000000000000000000000000000000:ℝ) ≤ (c 0) ∧ (c 0) ≤ (19884831127532564396512672002288043436143/40000000000000000000000000000000000000000:ℝ)) ∧
    ((-459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) ≤ (c 1) ∧ (c 1) ≤ (-918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ)) ∧
    ((1234520180703180068792731355451751117895833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 2) ∧ (c 2) ≤ (1234520180703180069004251508737505228187500000000001/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((-4161777406927635362143581238916761502604166666667/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 3) ∧ (c 3) ≤ (-4161777406927635357862527093864712195312499999999/5000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((39922265513441371659851116188959344599454365079/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 4) ∧ (c 4) ≤ (1247570797295042869818386238581510688709077381/312500000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((-146160257601109609691114718155473878554894181/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 5) ∧ (c 5) ≤ (-36540064400277401888780140211957530674740961/2500000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((85490800910736897378737724212098111885221/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 6) ∧ (c 6) ≤ (21372700227684225231648365445263354965829/500000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((-1030962613461800709432405239423456134457/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 7) ∧ (c 7) ≤ (-515481306730900300826802260977625483957/5000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((209976980814952849833222282098211959/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 8) ∧ (c 8) ≤ (2099769808149529002990533903117194979/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((-919535273875192780262580786685767/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 9) ∧ (c 9) ≤ (-3678141095500769229851175712561149/10000000000000000000000000000000000000000000000000000000:ℝ)) := by
  have hA0 : (115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 0 ∧ completedNativeThetaTailMoment 0 ≤ (57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨0,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA1 : (247320713366732650218889654413503763/1000000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 2 ∧ completedNativeThetaTailMoment 2 ≤ (2473207133667326502607677522105484947/10000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨1,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA2 : (4000101370527710015207524445255511/200000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 4 ∧ completedNativeThetaTailMoment 4 ≤ (100002534263192750482411997556849461/5000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨2,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA3 : (5754071852616085966370295496664877/2000000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 6 ∧ completedNativeThetaTailMoment 6 ≤ (5754071852616085991398122174464751/2000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨3,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA4 : (1474373230547965236999548382721929/2500000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 8 ∧ completedNativeThetaTailMoment 8 ≤ (5897492922191861033942937309299143/10000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨4,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA5 : (776040428721882815494537188678519/5000000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 10 ∧ completedNativeThetaTailMoment 10 ≤ (1552080857443765695263706301153963/10000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨5,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA6 : (123521074954908160410478039005927/2500000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 12 ∧ completedNativeThetaTailMoment 12 ≤ (98816859963926538641550737088273/2000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨6,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA7 : (45783634487247840546360071464651/2500000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 14 ∧ completedNativeThetaTailMoment 14 ≤ (7325381517959656245580136266111/400000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨7,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA8 : (3079455788683529239640494208701/400000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 16 ∧ completedNativeThetaTailMoment 16 ≤ (9623299339636033816206051328717/1250000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨8,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  have hA9 : (36011790549172927647565520455659/10000000000000000000000000000000000000000:ℝ) ≤ completedNativeThetaTailMoment 18 ∧ completedNativeThetaTailMoment 18 ≤ (7202358109834593002361801435879/2000000000000000000000000000000000000000:ℝ) := by
    have hh := hb ⟨9,by decide⟩
    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh
    exact hh
  let v1 : ℝ := (completedNativeThetaTailMoment 0)*(1/((4/1:ℝ)))
  have hv1 : (115168872467435603487327997711956563857/40000000000000000000000000000000000000000:ℝ) ≤ v1 ∧ v1 ≤ (57584436233717801745537942864046919937/20000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA0 (show (1/4:ℝ) ≤ 1/((4/1:ℝ)) ∧ 1/((4/1:ℝ)) ≤ (1/4:ℝ) from enclose_inv (show (4/1:ℝ) ≤ (4/1:ℝ) ∧ (4/1:ℝ) ≤ (4/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v0 : ℝ := (completedNativeThetaTailMoment 0)/(4/1:ℝ)
  have hv0 : (115168872467435603487327997711956563857/40000000000000000000000000000000000000000:ℝ) ≤ v0 ∧ v0 ≤ (57584436233717801745537942864046919937/20000000000000000000000000000000000000000:ℝ) := by
    change (115168872467435603487327997711956563857/40000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 0)/(4/1:ℝ) ∧ (completedNativeThetaTailMoment 0)/(4/1:ℝ) ≤ (57584436233717801745537942864046919937/20000000000000000000000000000000000000000:ℝ)
    have hprod := hv1
    change (115168872467435603487327997711956563857/40000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 0)*(1/(4/1:ℝ)) ∧ (completedNativeThetaTailMoment 0)*(1/(4/1:ℝ)) ≤ (57584436233717801745537942864046919937/20000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v2 : ℝ := (-1/1:ℝ)*v0
  have hv2 : (-57584436233717801745537942864046919937/20000000000000000000000000000000000000000:ℝ) ≤ v2 ∧ v2 ≤ (-115168872467435603487327997711956563857/40000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v3 : ℝ := (1/2:ℝ)+v2
  have hv3 : (9942415563766282198254462057135953080063/20000000000000000000000000000000000000000:ℝ) ≤ v3 ∧ v3 ≤ (19884831127532564396512672002288043436143/40000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (1/2:ℝ) ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ (1/2:ℝ) from ⟨le_rfl,le_rfl⟩) hv2 (by norm_num) (by norm_num)
  have eC0 : (c 0) = v3 := by
    try dsimp only [v0,v1,v2,v3]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC0 : (9942415563766282198254462057135953080063/20000000000000000000000000000000000000000:ℝ) ≤ (c 0) ∧ (c 0) ≤ (19884831127532564396512672002288043436143/40000000000000000000000000000000000000000:ℝ) := by
    rw [eC0]
    exact hv3
  let v5 : ℝ := (completedNativeThetaTailMoment 0)*(1/((1/1:ℝ)))
  have hv5 : (115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ) ≤ v5 ∧ v5 ≤ (57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA0 (show (1/1:ℝ) ≤ 1/((1/1:ℝ)) ∧ 1/((1/1:ℝ)) ≤ (1/1:ℝ) from enclose_inv (show (1/1:ℝ) ≤ (1/1:ℝ) ∧ (1/1:ℝ) ≤ (1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v4 : ℝ := (completedNativeThetaTailMoment 0)/(1/1:ℝ)
  have hv4 : (115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ) ≤ v4 ∧ v4 ≤ (57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ) := by
    change (115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 0)/(1/1:ℝ) ∧ (completedNativeThetaTailMoment 0)/(1/1:ℝ) ≤ (57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ)
    have hprod := hv5
    change (115168872467435603487327997711956563857/10000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 0)*(1/(1/1:ℝ)) ∧ (completedNativeThetaTailMoment 0)*(1/(1/1:ℝ)) ≤ (57584436233717801745537942864046919937/5000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v7 : ℝ := (completedNativeThetaTailMoment 2)*(1/((8/1:ℝ)))
  have hv7 : (247320713366732650218889654413503763/8000000000000000000000000000000000000000:ℝ) ≤ v7 ∧ v7 ≤ (2473207133667326502607677522105484947/80000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA1 (show (1/8:ℝ) ≤ 1/((8/1:ℝ)) ∧ 1/((8/1:ℝ)) ≤ (1/8:ℝ) from enclose_inv (show (8/1:ℝ) ≤ (8/1:ℝ) ∧ (8/1:ℝ) ≤ (8/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := (completedNativeThetaTailMoment 2)/(8/1:ℝ)
  have hv6 : (247320713366732650218889654413503763/8000000000000000000000000000000000000000:ℝ) ≤ v6 ∧ v6 ≤ (2473207133667326502607677522105484947/80000000000000000000000000000000000000000:ℝ) := by
    change (247320713366732650218889654413503763/8000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 2)/(8/1:ℝ) ∧ (completedNativeThetaTailMoment 2)/(8/1:ℝ) ≤ (2473207133667326502607677522105484947/80000000000000000000000000000000000000000:ℝ)
    have hprod := hv7
    change (247320713366732650218889654413503763/8000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 2)*(1/(8/1:ℝ)) ∧ (completedNativeThetaTailMoment 2)*(1/(8/1:ℝ)) ≤ (2473207133667326502607677522105484947/80000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v8 : ℝ := (-1/1:ℝ)*v6
  have hv8 : (-2473207133667326502607677522105484947/80000000000000000000000000000000000000000:ℝ) ≤ v8 ∧ v8 ≤ (-247320713366732650218889654413503763/8000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := v4+v8
  have hv9 : (918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ) ≤ v9 ∧ v9 ≤ (459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv4 hv8 (by norm_num) (by norm_num)
  let v10 : ℝ := v9*(-1/1:ℝ)
  have hv10 : (-459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) ≤ v10 ∧ v10 ≤ (-918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv9 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC1 : (c 1) = v10 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 1 = 0+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC1 : (-459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) ≤ (c 1) ∧ (c 1) ≤ (-918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ) := by
    rw [eC1]
    exact hv10
  let v12 : ℝ := (completedNativeThetaTailMoment 2)*(1/((2/1:ℝ)))
  have hv12 : (247320713366732650218889654413503763/2000000000000000000000000000000000000000:ℝ) ≤ v12 ∧ v12 ≤ (2473207133667326502607677522105484947/20000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA1 (show (1/2:ℝ) ≤ 1/((2/1:ℝ)) ∧ 1/((2/1:ℝ)) ≤ (1/2:ℝ) from enclose_inv (show (2/1:ℝ) ≤ (2/1:ℝ) ∧ (2/1:ℝ) ≤ (2/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v11 : ℝ := (completedNativeThetaTailMoment 2)/(2/1:ℝ)
  have hv11 : (247320713366732650218889654413503763/2000000000000000000000000000000000000000:ℝ) ≤ v11 ∧ v11 ≤ (2473207133667326502607677522105484947/20000000000000000000000000000000000000000:ℝ) := by
    change (247320713366732650218889654413503763/2000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 2)/(2/1:ℝ) ∧ (completedNativeThetaTailMoment 2)/(2/1:ℝ) ≤ (2473207133667326502607677522105484947/20000000000000000000000000000000000000000:ℝ)
    have hprod := hv12
    change (247320713366732650218889654413503763/2000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 2)*(1/(2/1:ℝ)) ∧ (completedNativeThetaTailMoment 2)*(1/(2/1:ℝ)) ≤ (2473207133667326502607677522105484947/20000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v14 : ℝ := (completedNativeThetaTailMoment 4)*(1/((96/1:ℝ)))
  have hv14 : (2083386130483182299587252315237245312499999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v14 ∧ v14 ≤ (2083386130483182301716916615767697104166666666667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA2 (show (52083333333333333333333333333333333333333333333333333/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((96/1:ℝ)) ∧ 1/((96/1:ℝ)) ≤ (104166666666666666666666666666666666666666666666666667/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (96/1:ℝ) ≤ (96/1:ℝ) ∧ (96/1:ℝ) ≤ (96/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v13 : ℝ := (completedNativeThetaTailMoment 4)/(96/1:ℝ)
  have hv13 : (2083386130483182299587252315237245312499999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v13 ∧ v13 ≤ (2083386130483182301716916615767697104166666666667/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (2083386130483182299587252315237245312499999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 4)/(96/1:ℝ) ∧ (completedNativeThetaTailMoment 4)/(96/1:ℝ) ≤ (2083386130483182301716916615767697104166666666667/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv14
    change (2083386130483182299587252315237245312499999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 4)*(1/(96/1:ℝ)) ∧ (completedNativeThetaTailMoment 4)*(1/(96/1:ℝ)) ≤ (2083386130483182301716916615767697104166666666667/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v15 : ℝ := (-1/1:ℝ)*v13
  have hv15 : (-2083386130483182301716916615767697104166666666667/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v15 ∧ v15 ≤ (-2083386130483182299587252315237245312499999999999/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v16 : ℝ := v11+v15
  have hv16 : (1234520180703180068792731355451751117895833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v16 ∧ v16 ≤ (1234520180703180069004251508737505228187500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv11 hv15 (by norm_num) (by norm_num)
  let v17 : ℝ := v16*(1/1:ℝ)
  have hv17 : (1234520180703180068792731355451751117895833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v17 ∧ v17 ≤ (1234520180703180069004251508737505228187500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv16 (show (1/1:ℝ) ≤ (1/1:ℝ) ∧ (1/1:ℝ) ≤ (1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC2 : (c 2) = v17 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 2 = 1+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC2 : (1234520180703180068792731355451751117895833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 2) ∧ (c 2) ≤ (1234520180703180069004251508737505228187500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC2]
    exact hv17
  let v19 : ℝ := (completedNativeThetaTailMoment 4)*(1/((24/1:ℝ)))
  have hv19 : (8333544521932729198349009260948981249999999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v19 ∧ v19 ≤ (8333544521932729206867666463070788416666666666667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA2 (show (208333333333333333333333333333333333333333333333333333/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((24/1:ℝ)) ∧ 1/((24/1:ℝ)) ≤ (416666666666666666666666666666666666666666666666666667/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (24/1:ℝ) ≤ (24/1:ℝ) ∧ (24/1:ℝ) ≤ (24/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v18 : ℝ := (completedNativeThetaTailMoment 4)/(24/1:ℝ)
  have hv18 : (8333544521932729198349009260948981249999999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v18 ∧ v18 ≤ (8333544521932729206867666463070788416666666666667/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (8333544521932729198349009260948981249999999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 4)/(24/1:ℝ) ∧ (completedNativeThetaTailMoment 4)/(24/1:ℝ) ≤ (8333544521932729206867666463070788416666666666667/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv19
    change (8333544521932729198349009260948981249999999999999/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 4)*(1/(24/1:ℝ)) ∧ (completedNativeThetaTailMoment 4)*(1/(24/1:ℝ)) ≤ (8333544521932729206867666463070788416666666666667/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v21 : ℝ := (completedNativeThetaTailMoment 6)*(1/((2880/1:ℝ)))
  have hv21 : (9989708077458482580503985237265411458333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v21 ∧ v21 ≤ (9989708077458482623955073219556859375000000001/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA3 (show (1736111111111111111111111111111111111111111111111111/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((2880/1:ℝ)) ∧ 1/((2880/1:ℝ)) ≤ (3472222222222222222222222222222222222222222222222223/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (2880/1:ℝ) ≤ (2880/1:ℝ) ∧ (2880/1:ℝ) ≤ (2880/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v20 : ℝ := (completedNativeThetaTailMoment 6)/(2880/1:ℝ)
  have hv20 : (9989708077458482580503985237265411458333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v20 ∧ v20 ≤ (9989708077458482623955073219556859375000000001/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (9989708077458482580503985237265411458333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 6)/(2880/1:ℝ) ∧ (completedNativeThetaTailMoment 6)/(2880/1:ℝ) ≤ (9989708077458482623955073219556859375000000001/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv21
    change (9989708077458482580503985237265411458333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 6)*(1/(2880/1:ℝ)) ∧ (completedNativeThetaTailMoment 6)*(1/(2880/1:ℝ)) ≤ (9989708077458482623955073219556859375000000001/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v22 : ℝ := (-1/1:ℝ)*v20
  have hv22 : (-9989708077458482623955073219556859375000000001/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v22 ∧ v22 ≤ (-9989708077458482580503985237265411458333333333/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v23 : ℝ := v18+v22
  have hv23 : (4161777406927635357862527093864712195312499999999/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v23 ∧ v23 ≤ (4161777406927635362143581238916761502604166666667/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv18 hv22 (by norm_num) (by norm_num)
  let v24 : ℝ := v23*(-1/1:ℝ)
  have hv24 : (-4161777406927635362143581238916761502604166666667/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v24 ∧ v24 ≤ (-4161777406927635357862527093864712195312499999999/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv23 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC3 : (c 3) = v24 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 3 = 2+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC3 : (-4161777406927635362143581238916761502604166666667/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 3) ∧ (c 3) ≤ (-4161777406927635357862527093864712195312499999999/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC3]
    exact hv24
  let v26 : ℝ := (completedNativeThetaTailMoment 6)*(1/((720/1:ℝ)))
  have hv26 : (39958832309833930322015940949061645833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v26 ∧ v26 ≤ (39958832309833930495820292878227437500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA3 (show (1736111111111111111111111111111111111111111111111111/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((720/1:ℝ)) ∧ 1/((720/1:ℝ)) ≤ (13888888888888888888888888888888888888888888888888889/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (720/1:ℝ) ≤ (720/1:ℝ) ∧ (720/1:ℝ) ≤ (720/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v25 : ℝ := (completedNativeThetaTailMoment 6)/(720/1:ℝ)
  have hv25 : (39958832309833930322015940949061645833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v25 ∧ v25 ≤ (39958832309833930495820292878227437500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (39958832309833930322015940949061645833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 6)/(720/1:ℝ) ∧ (completedNativeThetaTailMoment 6)/(720/1:ℝ) ≤ (39958832309833930495820292878227437500000000001/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv26
    change (39958832309833930322015940949061645833333333333/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 6)*(1/(720/1:ℝ)) ∧ (completedNativeThetaTailMoment 6)*(1/(720/1:ℝ)) ≤ (39958832309833930495820292878227437500000000001/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v28 : ℝ := (completedNativeThetaTailMoment 8)*(1/((161280/1:ℝ)))
  have hv28 : (36566796392558661631933243619095461309523809/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v28 ∧ v28 ≤ (18283398196279331082412380051150616939484127/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA4 (show (3875248015873015873015873015873015873015873015873/625000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((161280/1:ℝ)) ∧ 1/((161280/1:ℝ)) ≤ (62003968253968253968253968253968253968253968253969/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (161280/1:ℝ) ≤ (161280/1:ℝ) ∧ (161280/1:ℝ) ≤ (161280/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v27 : ℝ := (completedNativeThetaTailMoment 8)/(161280/1:ℝ)
  have hv27 : (36566796392558661631933243619095461309523809/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v27 ∧ v27 ≤ (18283398196279331082412380051150616939484127/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (36566796392558661631933243619095461309523809/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 8)/(161280/1:ℝ) ∧ (completedNativeThetaTailMoment 8)/(161280/1:ℝ) ≤ (18283398196279331082412380051150616939484127/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv28
    change (36566796392558661631933243619095461309523809/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 8)*(1/(161280/1:ℝ)) ∧ (completedNativeThetaTailMoment 8)*(1/(161280/1:ℝ)) ≤ (18283398196279331082412380051150616939484127/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v29 : ℝ := (-1/1:ℝ)*v27
  have hv29 : (-18283398196279331082412380051150616939484127/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v29 ∧ v29 ≤ (-36566796392558661631933243619095461309523809/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v30 : ℝ := v25+v29
  have hv30 : (39922265513441371659851116188959344599454365079/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v30 ∧ v30 ≤ (1247570797295042869818386238581510688709077381/312500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv25 hv29 (by norm_num) (by norm_num)
  let v31 : ℝ := v30*(1/1:ℝ)
  have hv31 : (39922265513441371659851116188959344599454365079/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v31 ∧ v31 ≤ (1247570797295042869818386238581510688709077381/312500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv30 (show (1/1:ℝ) ≤ (1/1:ℝ) ∧ (1/1:ℝ) ≤ (1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC4 : (c 4) = v31 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 4 = 3+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC4 : (39922265513441371659851116188959344599454365079/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 4) ∧ (c 4) ≤ (1247570797295042869818386238581510688709077381/312500000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC4]
    exact hv31
  let v33 : ℝ := (completedNativeThetaTailMoment 8)*(1/((40320/1:ℝ)))
  have hv33 : (73133592785117323263866487238190922619047619/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v33 ∧ v33 ≤ (18283398196279331082412380051150616939484127/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA4 (show (248015873015873015873015873015873015873015873015873/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((40320/1:ℝ)) ∧ 1/((40320/1:ℝ)) ≤ (124007936507936507936507936507936507936507936507937/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (40320/1:ℝ) ≤ (40320/1:ℝ) ∧ (40320/1:ℝ) ≤ (40320/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v32 : ℝ := (completedNativeThetaTailMoment 8)/(40320/1:ℝ)
  have hv32 : (73133592785117323263866487238190922619047619/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v32 ∧ v32 ≤ (18283398196279331082412380051150616939484127/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    change (73133592785117323263866487238190922619047619/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 8)/(40320/1:ℝ) ∧ (completedNativeThetaTailMoment 8)/(40320/1:ℝ) ≤ (18283398196279331082412380051150616939484127/1250000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv33
    change (73133592785117323263866487238190922619047619/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 8)*(1/(40320/1:ℝ)) ∧ (completedNativeThetaTailMoment 8)*(1/(40320/1:ℝ)) ≤ (18283398196279331082412380051150616939484127/1250000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v35 : ℝ := (completedNativeThetaTailMoment 10)*(1/((14515200/1:ℝ)))
  have hv35 : (21385593825007793636864450746211392195767/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v35 ∧ v35 ≤ (53463984562519486306206814275861269565697/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA5 (show (688932980599647266313932980599647266313932980599/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((14515200/1:ℝ)) ∧ 1/((14515200/1:ℝ)) ≤ (3444664902998236331569664902998236331569664903/50000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (14515200/1:ℝ) ≤ (14515200/1:ℝ) ∧ (14515200/1:ℝ) ≤ (14515200/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v34 : ℝ := (completedNativeThetaTailMoment 10)/(14515200/1:ℝ)
  have hv34 : (21385593825007793636864450746211392195767/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v34 ∧ v34 ≤ (53463984562519486306206814275861269565697/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (21385593825007793636864450746211392195767/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 10)/(14515200/1:ℝ) ∧ (completedNativeThetaTailMoment 10)/(14515200/1:ℝ) ≤ (53463984562519486306206814275861269565697/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv35
    change (21385593825007793636864450746211392195767/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 10)*(1/(14515200/1:ℝ)) ∧ (completedNativeThetaTailMoment 10)*(1/(14515200/1:ℝ)) ≤ (53463984562519486306206814275861269565697/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v36 : ℝ := (-1/1:ℝ)*v34
  have hv36 : (-53463984562519486306206814275861269565697/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v36 ∧ v36 ≤ (-21385593825007793636864450746211392195767/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v37 : ℝ := v32+v36
  have hv37 : (36540064400277401888780140211957530674740961/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v37 ∧ v37 ≤ (146160257601109609691114718155473878554894181/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv32 hv36 (by norm_num) (by norm_num)
  let v38 : ℝ := v37*(-1/1:ℝ)
  have hv38 : (-146160257601109609691114718155473878554894181/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v38 ∧ v38 ≤ (-36540064400277401888780140211957530674740961/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv37 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC5 : (c 5) = v38 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 5 = 4+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC5 : (-146160257601109609691114718155473878554894181/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 5) ∧ (c 5) ≤ (-36540064400277401888780140211957530674740961/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC5]
    exact hv38
  let v40 : ℝ := (completedNativeThetaTailMoment 10)*(1/((3628800/1:ℝ)))
  have hv40 : (427711876500155872737289014924227843915343/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v40 ∧ v40 ≤ (213855938250077945224827257103445078262787/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA5 (show (1377865961199294532627865961199294532627865961199/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((3628800/1:ℝ)) ∧ 1/((3628800/1:ℝ)) ≤ (2755731922398589065255731922398589065255731922399/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (3628800/1:ℝ) ≤ (3628800/1:ℝ) ∧ (3628800/1:ℝ) ≤ (3628800/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v39 : ℝ := (completedNativeThetaTailMoment 10)/(3628800/1:ℝ)
  have hv39 : (427711876500155872737289014924227843915343/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v39 ∧ v39 ≤ (213855938250077945224827257103445078262787/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (427711876500155872737289014924227843915343/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 10)/(3628800/1:ℝ) ∧ (completedNativeThetaTailMoment 10)/(3628800/1:ℝ) ≤ (213855938250077945224827257103445078262787/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv40
    change (427711876500155872737289014924227843915343/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 10)*(1/(3628800/1:ℝ)) ∧ (completedNativeThetaTailMoment 10)*(1/(3628800/1:ℝ)) ≤ (213855938250077945224827257103445078262787/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v42 : ℝ := (completedNativeThetaTailMoment 12)*(1/((1916006400/1:ℝ)))
  have hv42 : (128935973235692908343602650811528604497/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v42 ∧ v42 ≤ (128935973235692921800196931868642244619/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA6 (show (5219189246967024744802522580300358078135855913/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((1916006400/1:ℝ)) ∧ 1/((1916006400/1:ℝ)) ≤ (2609594623483512372401261290150179039067927957/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (1916006400/1:ℝ) ≤ (1916006400/1:ℝ) ∧ (1916006400/1:ℝ) ≤ (1916006400/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v41 : ℝ := (completedNativeThetaTailMoment 12)/(1916006400/1:ℝ)
  have hv41 : (128935973235692908343602650811528604497/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v41 ∧ v41 ≤ (128935973235692921800196931868642244619/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (128935973235692908343602650811528604497/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 12)/(1916006400/1:ℝ) ∧ (completedNativeThetaTailMoment 12)/(1916006400/1:ℝ) ≤ (128935973235692921800196931868642244619/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv42
    change (128935973235692908343602650811528604497/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 12)*(1/(1916006400/1:ℝ)) ∧ (completedNativeThetaTailMoment 12)*(1/(1916006400/1:ℝ)) ≤ (128935973235692921800196931868642244619/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v43 : ℝ := (-1/1:ℝ)*v41
  have hv43 : (-128935973235692921800196931868642244619/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v43 ∧ v43 ≤ (-128935973235692908343602650811528604497/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v44 : ℝ := v39+v43
  have hv44 : (85490800910736897378737724212098111885221/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v44 ∧ v44 ≤ (21372700227684225231648365445263354965829/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv39 hv43 (by norm_num) (by norm_num)
  let v45 : ℝ := v44*(1/1:ℝ)
  have hv45 : (85490800910736897378737724212098111885221/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v45 ∧ v45 ≤ (21372700227684225231648365445263354965829/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv44 (show (1/1:ℝ) ≤ (1/1:ℝ) ∧ (1/1:ℝ) ≤ (1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC6 : (c 6) = v45 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 6 = 5+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC6 : (85490800910736897378737724212098111885221/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 6) ∧ (c 6) ≤ (21372700227684225231648365445263354965829/500000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC6]
    exact hv45
  let v47 : ℝ := (completedNativeThetaTailMoment 12)*(1/((479001600/1:ℝ)))
  have hv47 : (515743892942771633374410603246114417989/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v47 ∧ v47 ≤ (1031487785885543374401575454949137956951/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA6 (show (10438378493934049489605045160600716156271711827/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((479001600/1:ℝ)) ∧ 1/((479001600/1:ℝ)) ≤ (4175351397573619795842018064240286462508684731/2000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (479001600/1:ℝ) ≤ (479001600/1:ℝ) ∧ (479001600/1:ℝ) ≤ (479001600/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v46 : ℝ := (completedNativeThetaTailMoment 12)/(479001600/1:ℝ)
  have hv46 : (515743892942771633374410603246114417989/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v46 ∧ v46 ≤ (1031487785885543374401575454949137956951/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (515743892942771633374410603246114417989/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 12)/(479001600/1:ℝ) ∧ (completedNativeThetaTailMoment 12)/(479001600/1:ℝ) ≤ (1031487785885543374401575454949137956951/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv47
    change (515743892942771633374410603246114417989/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 12)*(1/(479001600/1:ℝ)) ∧ (completedNativeThetaTailMoment 12)*(1/(479001600/1:ℝ)) ≤ (1031487785885543374401575454949137956951/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v49 : ℝ := (completedNativeThetaTailMoment 14)*(1/((348713164800/1:ℝ)))
  have hv49 : (262586211871332484585107762840911247/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v49 ∧ v49 ≤ (16411638241958284225521391780558377/312500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA7 (show (229414911954594494277033959573642113324653/80000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((348713164800/1:ℝ)) ∧ 1/((348713164800/1:ℝ)) ≤ (14338431997162155892314622473352632082790813/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (348713164800/1:ℝ) ≤ (348713164800/1:ℝ) ∧ (348713164800/1:ℝ) ≤ (348713164800/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v48 : ℝ := (completedNativeThetaTailMoment 14)/(348713164800/1:ℝ)
  have hv48 : (262586211871332484585107762840911247/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v48 ∧ v48 ≤ (16411638241958284225521391780558377/312500000000000000000000000000000000000000000000000000:ℝ) := by
    change (262586211871332484585107762840911247/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 14)/(348713164800/1:ℝ) ∧ (completedNativeThetaTailMoment 14)/(348713164800/1:ℝ) ≤ (16411638241958284225521391780558377/312500000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv49
    change (262586211871332484585107762840911247/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 14)*(1/(348713164800/1:ℝ)) ∧ (completedNativeThetaTailMoment 14)*(1/(348713164800/1:ℝ)) ≤ (16411638241958284225521391780558377/312500000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v50 : ℝ := (-1/1:ℝ)*v48
  have hv50 : (-16411638241958284225521391780558377/312500000000000000000000000000000000000000000000000000:ℝ) ≤ v50 ∧ v50 ≤ (-262586211871332484585107762840911247/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v51 : ℝ := v46+v50
  have hv51 : (515481306730900300826802260977625483957/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v51 ∧ v51 ≤ (1030962613461800709432405239423456134457/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv46 hv50 (by norm_num) (by norm_num)
  let v52 : ℝ := v51*(-1/1:ℝ)
  have hv52 : (-1030962613461800709432405239423456134457/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v52 ∧ v52 ≤ (-515481306730900300826802260977625483957/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv51 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC7 : (c 7) = v52 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 7 = 6+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC7 : (-1030962613461800709432405239423456134457/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 7) ∧ (c 7) ≤ (-515481306730900300826802260977625483957/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC7]
    exact hv52
  let v54 : ℝ := (completedNativeThetaTailMoment 14)*(1/((87178291200/1:ℝ)))
  have hv54 : (2100689694970659876680862102727289979/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v54 ∧ v54 ≤ (420137938994132076173347629582294451/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA7 (show (114707455977297247138516979786821056662326503/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((87178291200/1:ℝ)) ∧ 1/((87178291200/1:ℝ)) ≤ (14338431997162155892314622473352632082790813/1250000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (87178291200/1:ℝ) ≤ (87178291200/1:ℝ) ∧ (87178291200/1:ℝ) ≤ (87178291200/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v53 : ℝ := (completedNativeThetaTailMoment 14)/(87178291200/1:ℝ)
  have hv53 : (2100689694970659876680862102727289979/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v53 ∧ v53 ≤ (420137938994132076173347629582294451/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (2100689694970659876680862102727289979/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 14)/(87178291200/1:ℝ) ∧ (completedNativeThetaTailMoment 14)/(87178291200/1:ℝ) ≤ (420137938994132076173347629582294451/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv54
    change (2100689694970659876680862102727289979/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 14)*(1/(87178291200/1:ℝ)) ∧ (completedNativeThetaTailMoment 14)*(1/(87178291200/1:ℝ)) ≤ (420137938994132076173347629582294451/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v56 : ℝ := (completedNativeThetaTailMoment 16)*(1/((83691159552000/1:ℝ)))
  have hv56 : (229971705282844469051061198569319/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v56 ∧ v56 ≤ (919886821131378348639281745170389/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA8 (show (119486933309684632435955187277938600689923/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((83691159552000/1:ℝ)) ∧ 1/((83691159552000/1:ℝ)) ≤ (29871733327421158108988796819484650172481/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (83691159552000/1:ℝ) ≤ (83691159552000/1:ℝ) ∧ (83691159552000/1:ℝ) ≤ (83691159552000/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v55 : ℝ := (completedNativeThetaTailMoment 16)/(83691159552000/1:ℝ)
  have hv55 : (229971705282844469051061198569319/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v55 ∧ v55 ≤ (919886821131378348639281745170389/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (229971705282844469051061198569319/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 16)/(83691159552000/1:ℝ) ∧ (completedNativeThetaTailMoment 16)/(83691159552000/1:ℝ) ≤ (919886821131378348639281745170389/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv56
    change (229971705282844469051061198569319/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 16)*(1/(83691159552000/1:ℝ)) ∧ (completedNativeThetaTailMoment 16)*(1/(83691159552000/1:ℝ)) ≤ (919886821131378348639281745170389/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v57 : ℝ := (-1/1:ℝ)*v55
  have hv57 : (-919886821131378348639281745170389/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v57 ∧ v57 ≤ (-229971705282844469051061198569319/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v58 : ℝ := v53+v57
  have hv58 : (209976980814952849833222282098211959/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v58 ∧ v58 ≤ (2099769808149529002990533903117194979/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv53 hv57 (by norm_num) (by norm_num)
  let v59 : ℝ := v58*(1/1:ℝ)
  have hv59 : (209976980814952849833222282098211959/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v59 ∧ v59 ≤ (2099769808149529002990533903117194979/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv58 (show (1/1:ℝ) ≤ (1/1:ℝ) ∧ (1/1:ℝ) ≤ (1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC8 : (c 8) = v59 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 8 = 7+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC8 : (209976980814952849833222282098211959/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 8) ∧ (c 8) ≤ (2099769808149529002990533903117194979/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC8]
    exact hv59
  let v61 : ℝ := (completedNativeThetaTailMoment 16)*(1/((20922789888000/1:ℝ)))
  have hv61 : (3679547284525511504816979177109107/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v61 ∧ v61 ≤ (735909456905102678911425396136311/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA8 (show (477947733238738529743820749111754402759693/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((20922789888000/1:ℝ)) ∧ 1/((20922789888000/1:ℝ)) ≤ (238973866619369264871910374555877201379847/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (20922789888000/1:ℝ) ≤ (20922789888000/1:ℝ) ∧ (20922789888000/1:ℝ) ≤ (20922789888000/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v60 : ℝ := (completedNativeThetaTailMoment 16)/(20922789888000/1:ℝ)
  have hv60 : (3679547284525511504816979177109107/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v60 ∧ v60 ≤ (735909456905102678911425396136311/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (3679547284525511504816979177109107/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 16)/(20922789888000/1:ℝ) ∧ (completedNativeThetaTailMoment 16)/(20922789888000/1:ℝ) ≤ (735909456905102678911425396136311/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv61
    change (3679547284525511504816979177109107/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 16)*(1/(20922789888000/1:ℝ)) ∧ (completedNativeThetaTailMoment 16)*(1/(20922789888000/1:ℝ)) ≤ (735909456905102678911425396136311/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v63 : ℝ := (completedNativeThetaTailMoment 18)*(1/((25609494822912000/1:ℝ)))
  have hv63 : (1406189024742273506803833938487/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v63 ∧ v63 ≤ (703094512371137482901732273979/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hA9 (show (390480174214655661555409108751433335587/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((25609494822912000/1:ℝ)) ∧ 1/((25609494822912000/1:ℝ)) ≤ (97620043553663915388852277187858333897/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (25609494822912000/1:ℝ) ≤ (25609494822912000/1:ℝ) ∧ (25609494822912000/1:ℝ) ≤ (25609494822912000/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v62 : ℝ := (completedNativeThetaTailMoment 18)/(25609494822912000/1:ℝ)
  have hv62 : (1406189024742273506803833938487/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v62 ∧ v62 ≤ (703094512371137482901732273979/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (1406189024742273506803833938487/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 18)/(25609494822912000/1:ℝ) ∧ (completedNativeThetaTailMoment 18)/(25609494822912000/1:ℝ) ≤ (703094512371137482901732273979/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv63
    change (1406189024742273506803833938487/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (completedNativeThetaTailMoment 18)*(1/(25609494822912000/1:ℝ)) ∧ (completedNativeThetaTailMoment 18)*(1/(25609494822912000/1:ℝ)) ≤ (703094512371137482901732273979/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v64 : ℝ := (-1/1:ℝ)*v62
  have hv64 : (-703094512371137482901732273979/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v64 ∧ v64 ≤ (-1406189024742273506803833938487/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v65 : ℝ := v60+v64
  have hv65 : (3678141095500769229851175712561149/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v65 ∧ v65 ≤ (919535273875192780262580786685767/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv60 hv64 (by norm_num) (by norm_num)
  let v66 : ℝ := v65*(-1/1:ℝ)
  have hv66 : (-919535273875192780262580786685767/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v66 ∧ v66 ≤ (-3678141095500769229851175712561149/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv65 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have eC9 : (c 9) = v66 := by
    try dsimp only [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66]
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
    rw [show 9 = 8+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
    norm_num [Nat.factorial] <;> ring
  have hC9 : (-919535273875192780262580786685767/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (c 9) ∧ (c 9) ≤ (-3678141095500769229851175712561149/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eC9]
    exact hv66
  exact ⟨hC0,hC1,hC2,hC3,hC4,hC5,hC6,hC7,hC8,hC9⟩

private theorem moment_enclosures (hb : material_fourth_theta_box) :
    ((115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 0) ∧ (h 0) ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 1) ∧ (h 1) ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 2) ∧ (h 2) ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 3) ∧ (h 3) ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 4) ∧ (h 4) ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 5) ∧ (h 5) ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 6) ∧ (h 6) ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 7) ∧ (h 7) ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 8) ∧ (h 8) ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ)) := by
  have hh := characteristic_enclosures hb
  have hC0 := hh.1
  have hC1 := hh.2.1
  have hC2 := hh.2.2.1
  have hC3 := hh.2.2.2.1
  have hC4 := hh.2.2.2.2.1
  have hC5 := hh.2.2.2.2.2.1
  have hC6 := hh.2.2.2.2.2.2.1
  have hC7 := hh.2.2.2.2.2.2.2.1
  have hC8 := hh.2.2.2.2.2.2.2.2.1
  have hC9 := hh.2.2.2.2.2.2.2.2.2
  let v67 : ℝ := (c 1)*(-1/1:ℝ)
  have hv67 : (918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ) ≤ v67 ∧ v67 ≤ (459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC1 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v68 : ℝ := (-1/1:ℝ)*(0/1:ℝ)
  have hv68 : (0/1:ℝ) ≤ v68 ∧ v68 ≤ (0/1:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v69 : ℝ := v67+v68
  have hv69 : (918877772605817501396016304173547025909/80000000000000000000000000000000000000000:ℝ) ≤ v69 ∧ v69 ≤ (459438886302908750713209094640307840681/40000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv67 hv68 (by norm_num) (by norm_num)
  let v71 : ℝ := v69*(1/((c 0)))
  have hv71 : (115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v71 ∧ v71 ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv69 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v70 : ℝ := v69/(c 0)
  have hv70 : (115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v70 ∧ v70 ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v69/(c 0) ∧ v69/(c 0) ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv71
    change (115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v69*(1/(c 0)) ∧ v69*(1/(c 0)) ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH0 : (h 0) = v70 := by
    try dsimp only [v67,v68,v69,v70,v71]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH0 : (115524965577094853942901580704602956108231410402284367/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 0) ∧ (h 0) ≤ (46209986230837941578698240258725370856971412056015311/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH0]
    exact hv70
  let v72 : ℝ := (h 0)*(c 1)
  have hv72 : (-1326916538123058245319244725865166651623054724266077/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v72 ∧ v72 ≤ (-3317291345307645613077975526762179127337186753067/12500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v73 : ℝ := (0/1:ℝ)+v72
  have hv73 : (-1326916538123058245319244725865166651623054724266077/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v73 ∧ v73 ≤ (-3317291345307645613077975526762179127337186753067/12500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv72 (by norm_num) (by norm_num)
  let v74 : ℝ := (c 2)*(-2/1:ℝ)
  have hv74 : (-1234520180703180069004251508737505228187500000000001/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v74 ∧ v74 ≤ (-1234520180703180068792731355451751117895833333333333/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC2 (show (-2/1:ℝ) ≤ (-2/1:ℝ) ∧ (-2/1:ℝ) ≤ (-2/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v75 : ℝ := (-1/1:ℝ)*v73
  have hv75 : (3317291345307645613077975526762179127337186753067/12500000000000000000000000000000000000000000000000000:ℝ) ≤ v75 ∧ v75 ≤ (1326916538123058245319244725865166651623054724266077/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v76 : ℝ := v74+v75
  have hv76 : (92396357419878176226938701967366422747374701226799/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v76 ∧ v76 ≤ (11549544677484772065814171301676941715902673866593/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv74 hv75 (by norm_num) (by norm_num)
  let v78 : ℝ := v76*(1/((c 0)))
  have hv78 : (185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v78 ∧ v78 ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv76 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v77 : ℝ := v76/(c 0)
  have hv77 : (185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v77 ∧ v77 ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v76/(c 0) ∧ v76/(c 0) ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv78
    change (185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v76*(1/(c 0)) ∧ v76*(1/(c 0)) ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH1 : (h 1) = v77 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 1
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH1 : (185862996426348430540116847619902852977134628077213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 1) ∧ (h 1) ≤ (371725992852696862285542732533694490590825883248553/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH1]
    exact hv77
  let v79 : ℝ := (h 0)*(c 2)
  have hv79 : (5704716055198551848337762012887914508577994496963/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v79 ∧ v79 ≤ (713089506899818981188127144715403658890811541861/250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v80 : ℝ := (0/1:ℝ)+v79
  have hv80 : (5704716055198551848337762012887914508577994496963/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v80 ∧ v80 ≤ (713089506899818981188127144715403658890811541861/250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv79 (by norm_num) (by norm_num)
  let v81 : ℝ := (h 1)*(c 1)
  have hv81 : (-853926880830430323034014332206269594102890627063/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v81 ∧ v81 ≤ (-4269634404152151601184660980827729730204651036319/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v82 : ℝ := v80+v81
  have hv82 : (48507891743681215253037476806816449144751038699/20000000000000000000000000000000000000000000000000000:ℝ) ≤ v82 ∧ v82 ≤ (24253945871840607646340424807788416625427810638121/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv80 hv81 (by norm_num) (by norm_num)
  let v83 : ℝ := (c 3)*(-3/1:ℝ)
  have hv83 : (12485332220782906073587581281594136585937499999997/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v83 ∧ v83 ≤ (12485332220782906086430743716750284507812500000001/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC3 (show (-3/1:ℝ) ≤ (-3/1:ℝ) ∧ (-3/1:ℝ) ≤ (-3/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v84 : ℝ := (-1/1:ℝ)*v82
  have hv84 : (-24253945871840607646340424807788416625427810638121/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v84 ∧ v84 ≤ (-48507891743681215253037476806816449144751038699/20000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv82 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v85 : ℝ := v83+v84
  have hv85 : (716718569725204500834737755399856546447189361873/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v85 ∧ v85 ≤ (358359284862602273171374515046172221624740325251/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv83 hv84 (by norm_num) (by norm_num)
  let v87 : ℝ := v85*(1/((c 0)))
  have hv87 : (90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v87 ∧ v87 ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv85 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v86 : ℝ := v85/(c 0)
  have hv86 : (90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v86 ∧ v86 ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v85/(c 0) ∧ v85/(c 0) ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv87
    change (90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v85*(1/(c 0)) ∧ v85*(1/(c 0)) ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH2 : (h 2) = v86 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 2
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH2 : (90108707125608296993004566157073242335069893337/625000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 2) ∧ (h 2) ≤ (1441739314009732843431513522775964497526459113753/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH2]
    exact hv86
  let v88 : ℝ := (h 0)*(c 3)
  have hv88 : (-192315676669938463021667563773763638224222174489/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v88 ∧ v88 ≤ (-192315676669938462817440928538528418687610808869/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v89 : ℝ := (0/1:ℝ)+v88
  have hv89 : (-192315676669938463021667563773763638224222174489/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v89 ∧ v89 ≤ (-192315676669938462817440928538528418687610808869/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv88 (by norm_num) (by norm_num)
  let v90 : ℝ := (h 1)*(c 2)
  have hv90 : (9178064797371607033048216776361233949296683723/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v90 ∧ v90 ≤ (45890323986858035321901670832979086166832158917/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v91 : ℝ := v89+v90
  have hv91 : (-73212676341540213928213239945978734238869377937/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v91 ∧ v91 ≤ (-4575792271346263359235601803298416641274332811/312500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv89 hv90 (by norm_num) (by norm_num)
  let v92 : ℝ := (h 2)*(c 1)
  have hv92 : (-3311955523838756526022971222440651417677909631/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v92 ∧ v92 ≤ (-132478220953550252624812422552233381384945287/80000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v93 : ℝ := v91+v92
  have hv93 : (-162985130302274210486541336004160725566128304029/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v93 ∧ v93 ≤ (-162985130302274209073640810524578505193896810827/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv91 hv92 (by norm_num) (by norm_num)
  let v94 : ℝ := (c 4)*(-4/1:ℝ)
  have hv94 : (-1247570797295042869818386238581510688709077381/78125000000000000000000000000000000000000000000000000:ℝ) ≤ v94 ∧ v94 ≤ (-39922265513441371659851116188959344599454365079/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC4 (show (-4/1:ℝ) ≤ (-4/1:ℝ) ∧ (-4/1:ℝ) ≤ (-4/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v95 : ℝ := (-1/1:ℝ)*v93
  have hv95 : (162985130302274209073640810524578505193896810827/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v95 ∧ v95 ≤ (162985130302274210486541336004160725566128304029/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v96 : ℝ := v94+v95
  have hv96 : (3296068248508721736887371986145137039134906059/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v96 ∧ v96 ≤ (3296068248508723847136871248323347168310843713/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv94 hv95 (by norm_num) (by norm_num)
  let v98 : ℝ := v96*(1/((c 0)))
  have hv98 : (663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v98 ∧ v98 ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv96 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v97 : ℝ := v96/(c 0)
  have hv97 : (663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v97 ∧ v97 ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v96/(c 0) ∧ v96/(c 0) ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv98
    change (663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v96*(1/(c 0)) ∧ v96*(1/(c 0)) ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH3 : (h 3) = v97 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 3
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH3 : (663031680252990658495259901346491897088878339/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 3) ∧ (h 3) ≤ (6630316802529910829897113694195980879246706499/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH3]
    exact hv97
  let v99 : ℝ := (h 0)*(c 4)
  have hv99 : (922403669839991095221095452606666888195529813/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v99 ∧ v99 ≤ (922403669839991099279848659133886059678787541/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v100 : ℝ := (0/1:ℝ)+v99
  have hv100 : (922403669839991095221095452606666888195529813/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v100 ∧ v100 ≤ (922403669839991099279848659133886059678787541/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv99 (by norm_num) (by norm_num)
  let v101 : ℝ := (h 1)*(c 3)
  have hv101 : (-30940816772441949272503180196401957831965589/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v101 ∧ v101 ≤ (-77352041931104872850877599375953326426484841/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v102 : ℝ := v100+v101
  have hv102 : (612995502115571602496063650642647309875873923/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v102 ∧ v102 ≤ (612995502115571607876338261630072753972848177/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv100 hv101 (by norm_num) (by norm_num)
  let v103 : ℝ := (h 2)*(c 2)
  have hv103 : (177985627845817414861930848178632709449542547/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v103 ∧ v103 ≤ (88992813922908713096824503330813641995367961/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v104 : ℝ := v102+v103
  have hv104 : (79098112996138901735799449882128001932541647/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v104 ∧ v104 ≤ (790981129961389034069987268291700037963584099/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv102 hv103 (by norm_num) (by norm_num)
  let v105 : ℝ := (h 3)*(c 1)
  have hv105 : (-19038908547436282455339998633019511901911139/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v105 ∧ v105 ≤ (-76155634189745081061525811847489171238436583/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v106 : ℝ := v104+v105
  have hv106 : (357412747885821943768317252144600985858885957/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v106 ∧ v106 ≤ (178706373942910988252115364111052716681286879/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv104 hv105 (by norm_num) (by norm_num)
  let v107 : ℝ := (c 5)*(-5/1:ℝ)
  have hv107 : (36540064400277401888780140211957530674740961/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v107 ∧ v107 ≤ (146160257601109609691114718155473878554894181/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC5 (show (-5/1:ℝ) ≤ (-5/1:ℝ) ∧ (-5/1:ℝ) ≤ (-5/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v108 : ℝ := (-1/1:ℝ)*v106
  have hv108 : (-178706373942910988252115364111052716681286879/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v108 ∧ v108 ≤ (-357412747885821943768317252144600985858885957/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv106 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v109 : ℝ := v107+v108
  have hv109 : (1996974029238010595892668474367468346208963/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v109 ∧ v109 ≤ (15975792233904160918939086488167421056698991/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv107 hv108 (by norm_num) (by norm_num)
  let v111 : ℝ := v109*(1/((c 0)))
  have hv111 : (32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v111 ∧ v111 ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv109 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v110 : ℝ := v109/(c 0)
  have hv110 : (32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v110 ∧ v110 ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v109/(c 0) ∧ v109/(c 0) ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv111
    change (32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v109*(1/(c 0)) ∧ v109*(1/(c 0)) ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH4 : (h 4) = v110 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 4
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH4 : (32136641506165935647776173525850127274837591/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 4) ∧ (h 4) ≤ (6427328301233217766697792829962795734987709/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH4]
    exact hv110
  let v112 : ℝ := (h 0)*(c 5)
  have hv112 : (-3377031745621500826772150468146540656462429/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v112 ∧ v112 ≤ (-135081269824860031092306063199313143989481/400000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v113 : ℝ := (0/1:ℝ)+v112
  have hv113 : (-3377031745621500826772150468146540656462429/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v113 ∧ v113 ≤ (-135081269824860031092306063199313143989481/400000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv112 (by norm_num) (by norm_num)
  let v114 : ℝ := (h 1)*(c 4)
  have hv114 : (296802875698259474092439290880512775989133/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v114 ∧ v114 ≤ (1484014378491297381754631686765886724495531/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v115 : ℝ := v113+v114
  have hv115 : (-473254341782550864077488503435994194129191/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v115 ∧ v115 ≤ (-946508683565101697776509946608470937620747/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv113 hv114 (by norm_num) (by norm_num)
  let v116 : ℝ := (h 2)*(c 3)
  have hv116 : (-4687654768535198267623019845400684453247/39062500000000000000000000000000000000000000000000000:ℝ) ≤ v116 ∧ v116 ≤ (-1200039620745010679080375811838607655950131/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v117 : ℝ := v115+v116
  have hv117 : (-773264246968803553205361773541637999136999/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v117 ∧ v117 ≤ (-24744455903001712597067165640444396249533/80000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv115 hv116 (by norm_num) (by norm_num)
  let v118 : ℝ := (h 3)*(c 2)
  have hv118 : (818525989717855135795945013595520384535133/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v118 ∧ v118 ≤ (818525989717855659983156510098857058324761/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v119 : ℝ := v117+v118
  have hv119 : (-2274530998157359077025502080571031612012863/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v119 ∧ v119 ≤ (-142158187384834900915639949684793279554179/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv117 hv118 (by norm_num) (by norm_num)
  let v120 : ℝ := (h 4)*(c 1)
  have hv120 : (-46140071197214937235582004489432584059579/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v120 ∧ v120 ≤ (-369120569577717738385611303842539657637813/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v121 : ℝ := v119+v120
  have hv121 : (-528730313547015714982031623297298456897899/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v121 ∧ v121 ≤ (-2643651567735076153035850498799232130504677/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv119 hv120 (by norm_num) (by norm_num)
  let v122 : ℝ := (c 6)*(-6/1:ℝ)
  have hv122 : (-64118100683052675694945096335790064897487/250000000000000000000000000000000000000000000000000000:ℝ) ≤ v122 ∧ v122 ≤ (-256472402732210692136213172636294335655663/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC6 (show (-6/1:ℝ) ≤ (-6/1:ℝ) ∧ (-6/1:ℝ) ≤ (-6/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v123 : ℝ := (-1/1:ℝ)*v121
  have hv123 : (2643651567735076153035850498799232130504677/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v123 ∧ v123 ≤ (528730313547015714982031623297298456897899/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv121 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v124 : ℝ := v122+v123
  have hv124 : (78927540412969125238046645367629534605197/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v124 ∧ v124 ≤ (15785508082594330709605278024709785586573/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv122 hv123 (by norm_num) (by norm_num)
  let v126 : ℝ := v124*(1/((c 0)))
  have hv126 : (158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v126 ∧ v126 ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv124 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v125 : ℝ := v124/(c 0)
  have hv125 : (158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v125 ∧ v125 ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v124/(c 0) ∧ v124/(c 0) ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv126
    change (158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v124*(1/(c 0)) ∧ v124*(1/(c 0)) ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH5 : (h 5) = v125 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 5
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH5 : (158769345149098992850492503031152369571581/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 5) ∧ (h 5) ≤ (158769345149104078757389887334488148065689/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH5]
    exact hv125
  let v127 : ℝ := (h 0)*(c 6)
  have hv127 : (2469080458092787364732663640669337444079/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v127 ∧ v127 ≤ (2469080458092787467281298715351450811563/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v128 : ℝ := (0/1:ℝ)+v127
  have hv128 : (2469080458092787364732663640669337444079/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v128 ∧ v128 ≤ (2469080458092787467281298715351450811563/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv127 (by norm_num) (by norm_num)
  let v129 : ℝ := (h 1)*(c 5)
  have hv129 : (-8489307323809125470386756787039339937/15625000000000000000000000000000000000000000000000000:ℝ) ≤ v129 ∧ v129 ≤ (-5433156687237840204030241520448812378989/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v130 : ℝ := v128+v129
  have hv130 : (1110791286283327289470782554743043054159/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v130 ∧ v130 ≤ (4443165145133309665094953340956990867263/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv128 hv129 (by norm_num) (by norm_num)
  let v131 : ℝ := (h 2)*(c 4)
  have hv131 : (359734373094146090382155562857282065271/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v131 ∧ v131 ≤ (5755749969506337836711528405705478444623/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v132 : ℝ := v130+v131
  have hv132 : (2549728778659911650999404806172171315243/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v132 ∧ v132 ≤ (5099457557319823750903240873331234655943/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv130 hv131 (by norm_num) (by norm_num)
  let v133 : ℝ := (h 3)*(c 3)
  have hv133 : (-5518780533908332571860404505311044273469/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v133 ∧ v133 ≤ (-2759390266954164516440310243641383573081/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v134 : ℝ := v132+v133
  have hv134 : (4680134580731314032137214719377640987503/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v134 ∧ v134 ≤ (1170033645182829617231465314844925541431/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv132 hv133 (by norm_num) (by norm_num)
  let v135 : ℝ := (h 4)*(c 2)
  have hv135 : (3967333247938528777083416676978053427177/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v135 ∧ v135 ≤ (396733324793854768884855495337923375451/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v136 : ℝ := v134+v135
  have hv136 : (216186695716746070230515784908892360367/250000000000000000000000000000000000000000000000000000:ℝ) ≤ v136 ∧ v136 ≤ (4323733914334933078887208106379467960117/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv134 hv135 (by norm_num) (by norm_num)
  let v137 : ℝ := (h 5)*(c 1)
  have hv137 : (-455905069464665661456380594570952122773/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v137 ∧ v137 ≤ (-1823620277858604229180166922753390381061/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH5 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v138 : ℝ := v136+v137
  have hv138 : (1705961887702795040848777254517971480897/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v138 ∧ v138 ≤ (6823847550811261928594249290005545539173/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv136 hv137 (by norm_num) (by norm_num)
  let v139 : ℝ := (c 7)*(-7/1:ℝ)
  have hv139 : (3608369147116302105787615826843378387699/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v139 ∧ v139 ≤ (7216738294232604966026836675964192941199/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC7 (show (-7/1:ℝ) ≤ (-7/1:ℝ) ∧ (-7/1:ℝ) ≤ (-7/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v140 : ℝ := (-1/1:ℝ)*v138
  have hv140 : (-6823847550811261928594249290005545539173/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v140 ∧ v140 ≤ (-1705961887702795040848777254517971480897/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv138 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v141 : ℝ := v139+v140
  have hv141 : (15715629736853691319239294547248449449/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v141 ∧ v141 ≤ (392890743421424802631727657892307017611/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv139 hv140 (by norm_num) (by norm_num)
  let v143 : ℝ := v141*(1/((c 0)))
  have hv143 : (790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v143 ∧ v143 ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv141 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v142 : ℝ := v141/(c 0)
  have hv142 : (790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v142 ∧ v142 ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v141/(c 0) ∧ v141/(c 0) ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv143
    change (790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v141*(1/(c 0)) ∧ v141*(1/(c 0)) ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH6 : (h 6) = v142 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 6
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH6 : (790332572404590797597892821125714344609/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 6) ∧ (h 6) ≤ (790332572404756792773391373565608373777/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH6]
    exact hv142
  let v144 : ℝ := (h 0)*(c 7)
  have hv144 : (-23820384086289254926889361080340411239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v144 ∧ v144 ≤ (-4764076817257850487173660869192036807/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v145 : ℝ := (0/1:ℝ)+v144
  have hv145 : (-23820384086289254926889361080340411239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v145 ∧ v145 ≤ (-4764076817257850487173660869192036807/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv144 (by norm_num) (by norm_num)
  let v146 : ℝ := (h 1)*(c 6)
  have hv146 : (15889576424157957108467008349186171467/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v146 ∧ v146 ≤ (15889576424157957819403524093766589391/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v147 : ℝ := v145+v146
  have hv147 : (-1982701915532824454605588182788559943/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v147 ∧ v147 ≤ (-1982701915532823654116195063048398661/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv145 hv146 (by norm_num) (by norm_num)
  let v148 : ℝ := (h 2)*(c 5)
  have hv148 : (-2107249895293096092180167697529884027/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v148 ∧ v148 ≤ (-2634062369116369909480714733987225673/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v149 : ℝ := v147+v148
  have hv149 : (-14501653307531129370112014853226540021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v149 ∧ v149 ≤ (-7250826653765563473077624531022850007/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv147 hv148 (by norm_num) (by norm_num)
  let v150 : ℝ := (h 3)*(c 4)
  have hv150 : (26469726782883055474003611857004627179/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v150 ∧ v150 ≤ (5293945356576614507274985560103009431/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v151 : ℝ := v149+v150
  have hv151 : (-2533579832179203266220417849448452863/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v151 ∧ v151 ≤ (-2533579832179181355935570323576352873/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv149 hv150 (by norm_num) (by norm_num)
  let v152 : ℝ := (h 4)*(c 3)
  have hv152 : (-3343638713872373081806352274957416399/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v152 ∧ v152 ≤ (-26749109710978857121967366509153537099/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v153 : ℝ := v151+v152
  have hv153 : (-5856537908631637584134247209821556811/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v153 ∧ v153 ≤ (-7320672385789509619475734208182472493/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv151 hv152 (by norm_num) (by norm_num)
  let v154 : ℝ := (h 5)*(c 2)
  have hv154 : (19600396066359125453572905604624175179/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v154 ∧ v154 ≤ (19600396066359753322401397068930428331/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH5 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v155 : ℝ := v153+v154
  have hv155 : (-2420573369199765616774582611120902219/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v155 ∧ v155 ≤ (-9682293476798285155501539763799461641/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv153 hv154 (by norm_num) (by norm_num)
  let v156 : ℝ := (h 6)*(c 1)
  have hv156 : (-9077737921863861353195538392388302743/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v156 ∧ v156 ≤ (-4538868960930977368465562810567384177/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH6 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v157 : ℝ := v155+v156
  have hv157 : (-18760031398662923820293868836871911619/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v157 ∧ v157 ≤ (-3752006279732047978486533076986845999/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv155 hv156 (by norm_num) (by norm_num)
  let v158 : ℝ := (c 8)*(-8/1:ℝ)
  have hv158 : (-2099769808149529002990533903117194979/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v158 ∧ v158 ≤ (-209976980814952849833222282098211959/125000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC8 (show (-8/1:ℝ) ≤ (-8/1:ℝ) ∧ (-8/1:ℝ) ≤ (-8/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v159 : ℝ := (-1/1:ℝ)*v157
  have hv159 : (3752006279732047978486533076986845999/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v159 ∧ v159 ≤ (18760031398662923820293868836871911619/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv157 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v160 : ℝ := v158+v159
  have hv160 : (1961872933464007868508394159996670163/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v160 ∧ v160 ≤ (1961872933466695833636086269014954899/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv158 hv159 (by norm_num) (by norm_num)
  let v162 : ℝ := v160*(1/((c 0)))
  have hv162 : (197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v162 ∧ v162 ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv160 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v161 : ℝ := v160/(c 0)
  have hv161 : (197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v161 ∧ v161 ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    change (197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v160/(c 0) ∧ v160/(c 0) ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv162
    change (197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v160*(1/(c 0)) ∧ v160*(1/(c 0)) ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH7 : (h 7) = v161 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 7
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH7 : (197323569999807131328730395873194801/500000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 7) ∧ (h 7) ≤ (986617850000387423279648260040681171/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH7]
    exact hv161
  let v163 : ℝ := (h 0)*(c 8)
  have hv163 : (48515166961259469056819844350099363/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v163 ∧ v163 ≤ (2425758348062974035928047947255561/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v164 : ℝ := (0/1:ℝ)+v163
  have hv164 : (48515166961259469056819844350099363/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v164 ∧ v164 ≤ (2425758348062974035928047947255561/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv163 (by norm_num) (by norm_num)
  let v165 : ℝ := (h 1)*(c 7)
  have hv165 : (-38323560108309900845264489816102911/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v165 ∧ v165 ≤ (-7664712021661979342916692757391383/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v166 : ℝ := v164+v165
  have hv166 : (2547901713237392052888838633499113/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v166 ∧ v166 ≤ (2038321370589916800795499031630861/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv164 hv165 (by norm_num) (by norm_num)
  let v167 : ℝ := (h 2)*(c 6)
  have hv167 : (15406931082398556301910822147463763/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v167 ∧ v167 ≤ (6162772432959423167824585894102849/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v168 : ℝ := v166+v167
  have hv168 : (4488708198908987088699915195240719/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v168 ∧ v168 ≤ (14363866236508763136444670819836559/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv166 hv167 (by norm_num) (by norm_num)
  let v169 : ℝ := (h 3)*(c 5)
  have hv169 : (-48454440591736858119101992956409279/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v169 ∧ v169 ≤ (-96908881183473652777753813967274139/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v170 : ℝ := v168+v169
  have hv170 : (-12544775000464961409502671394483527/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v170 ∧ v170 ≤ (-1568096875058114818470653741755709/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv168 hv169 (by norm_num) (by norm_num)
  let v171 : ℝ := (h 4)*(c 4)
  have hv171 : (1282967534919436912370208781084977/100000000000000000000000000000000000000000000000000000:ℝ) ≤ v171 ∧ v171 ≤ (2004636773311629739833626824895151/156250000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v172 : ℝ := v170+v171
  have hv172 : (51603601745506884209007767659765323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v172 ∧ v172 ≤ (1290090043637680828172770711564979/125000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv170 hv171 (by norm_num) (by norm_num)
  let v173 : ℝ := (h 5)*(c 3)
  have hv173 : (-264305069421694846039855277597543/20000000000000000000000000000000000000000000000000000:ℝ) ≤ v173 ∧ v173 ≤ (-6607626735542159480075187594148993/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH5 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v174 : ℝ := v172+v173
  have hv174 : (-14472665609916827300956051739620427/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v174 ∧ v174 ≤ (-1447266560991436167384104747889077/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv172 hv173 (by norm_num) (by norm_num)
  let v175 : ℝ := (h 6)*(c 2)
  have hv175 : (12196018876256557211368633813798071/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v175 ∧ v175 ≤ (19513630202014590029414286020247759/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH6 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v176 : ℝ := v174+v175
  have hv176 : (34311409895109401544518483515571857/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v176 ∧ v176 ≤ (13724563958048845359877867028691451/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv174 hv175 (by norm_num) (by norm_num)
  let v177 : ℝ := (h 7)*(c 1)
  have hv177 : (-45329060621074827769498174052103139/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v177 ∧ v177 ≤ (-45329060621012722352220065862460827/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH7 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v178 : ℝ := v176+v177
  have hv178 : (931750366765759012781551719161623/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v178 ∧ v178 ≤ (5823439792307876111792317320249107/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv176 hv177 (by norm_num) (by norm_num)
  let v179 : ℝ := (c 9)*(-9/1:ℝ)
  have hv179 : (33103269859506923068660581413050341/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v179 ∧ v179 ≤ (8275817464876735022363227080171903/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC9 (show (-9/1:ℝ) ≤ (-9/1:ℝ) ∧ (-9/1:ℝ) ≤ (-9/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v180 : ℝ := (-1/1:ℝ)*v178
  have hv180 : (-5823439792307876111792317320249107/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v180 ∧ v180 ≤ (-931750366765759012781551719161623/400000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv178 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v181 : ℝ := v179+v180
  have hv181 : (9809510690275418621491312132053913/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v181 ∧ v181 ≤ (9809510690362964769914115341647037/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv179 hv180 (by norm_num) (by norm_num)
  let v183 : ℝ := v181*(1/((c 0)))
  have hv183 : (1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v183 ∧ v183 ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv181 (show (10057917953503750215425116204795799738548194324065379897/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((c 0)) ∧ 1/((c 0)) ≤ (20115835907007500430854023837331011837241039659669999967/10000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hC0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v182 : ℝ := v181/(c 0)
  have hv182 : (1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v182 ∧ v182 ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v181/(c 0) ∧ v181/(c 0) ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv183
    change (1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v181*(1/(c 0)) ∧ v181*(1/(c 0)) ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eH8 : (h 8) = v182 := by
    try dsimp only [v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 8
    norm_num [Finset.sum_range_succ] at he
    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
    try simp only [zero_add]
    linarith only [he]
  have hH8 : (1233290671085101232389115030273209/625000000000000000000000000000000000000000000000000000:ℝ) ≤ (h 8) ∧ (h 8) ≤ (19732650737537726113825922974961561/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eH8]
    exact hv182
  exact ⟨hH0,hH1,hH2,hH3,hH4,hH5,hH6,hH7,hH8⟩

/-- Kernel-checked arithmetic implication for the actual theta moments.
This theorem does not assert `material_fourth_theta_box`. -/
theorem material_fourth_bounds_of_theta_box (hb : material_fourth_theta_box) :
    ((833/50000000000000000000000000000:ℝ) < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < (1667/100000000000000000000000000000:ℝ)) ∧
    ((-36781318917/100000000000000000000000000000000:ℝ) < material_fourth_characteristic_ceiling ∧ material_fourth_characteristic_ceiling < (-22988324323/62500000000000000000000000000000:ℝ)) ∧
    ((9203/10000000000000000000000000000000:ℝ) < material_fourth_characteristic_ceiling-c 9 ∧ material_fourth_characteristic_ceiling-c 9 < (2301/2500000000000000000000000000000:ℝ)) := by
  have hh := characteristic_enclosures hb
  have hC0 := hh.1
  have hC1 := hh.2.1
  have hC2 := hh.2.2.1
  have hC3 := hh.2.2.2.1
  have hC4 := hh.2.2.2.2.1
  have hC5 := hh.2.2.2.2.2.1
  have hC6 := hh.2.2.2.2.2.2.1
  have hC7 := hh.2.2.2.2.2.2.2.1
  have hC8 := hh.2.2.2.2.2.2.2.2.1
  have hC9 := hh.2.2.2.2.2.2.2.2.2
  have hh := moment_enclosures hb
  have hH0 := hh.1
  have hH1 := hh.2.1
  have hH2 := hh.2.2.1
  have hH3 := hh.2.2.2.1
  have hH4 := hh.2.2.2.2.1
  have hH5 := hh.2.2.2.2.2.1
  have hH6 := hh.2.2.2.2.2.2.1
  have hH7 := hh.2.2.2.2.2.2.2.1
  have hH8 := hh.2.2.2.2.2.2.2.2
  let v184 : ℝ := (h 1)*(h 1)
  have hv184 : (1727252672029040473097050760072103362843568413/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v184 ∧ v184 ≤ (13818021376232323874385345797056634395792668999/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hH1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v186 : ℝ := v184*(1/((h 0)))
  have hv186 : (598053472996317612151868247404179543462248926801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v186 ∧ v186 ≤ (598053472996317616050104665908638187705375108473/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv184 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v185 : ℝ := v184/(h 0)
  have hv185 : (598053472996317612151868247404179543462248926801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v185 ∧ v185 ≤ (598053472996317616050104665908638187705375108473/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (598053472996317612151868247404179543462248926801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v184/(h 0) ∧ v184/(h 0) ≤ (598053472996317616050104665908638187705375108473/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv186
    change (598053472996317612151868247404179543462248926801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v184*(1/(h 0)) ∧ v184*(1/(h 0)) ≤ (598053472996317616050104665908638187705375108473/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v187 : ℝ := (-1/1:ℝ)*v185
  have hv187 : (-598053472996317616050104665908638187705375108473/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v187 ∧ v187 ≤ (-598053472996317612151868247404179543462248926801/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv185 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v188 : ℝ := (h 2)+v187
  have hv188 : (843685841013415135837968392604533689655743184919/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v188 ∧ v188 ≤ (105460730126676903909955659421473119258026273369/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH2 hv187 (by norm_num) (by norm_num)
  have eR000 : (carryPairingRemainder carryMaterialEvenPairing 0 0 0) = v188 := by
    try dsimp only [v184,v185,v186,v187,v188]
    change carryMaterialEvenPairing 0 0 = _
    rw [material_even_pairing_source]
    ring
  have hR000 : (843685841013415135837968392604533689655743184919/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (105460730126676903909955659421473119258026273369/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR000]
    exact hv188
  let v189 : ℝ := (h 1)*(h 2)
  have hv189 : (53593197793503399240255234436363802015604119/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v189 ∧ v189 ≤ (26796598896751701408468503234564610442009439/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hH2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v191 : ℝ := v189*(1/((h 0)))
  have hv191 : (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v191 ∧ v191 ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv189 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v190 : ℝ := v189/(h 0)
  have hv190 : (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v190 ∧ v190 ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v189/(h 0) ∧ v189/(h 0) ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv191
    change (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v189*(1/(h 0)) ∧ v189*(1/(h 0)) ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v192 : ℝ := (-1/1:ℝ)*v190
  have hv192 : (-2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v192 ∧ v192 ≤ (-92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv190 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v193 : ℝ := (h 3)+v192
  have hv193 : (4310766325895558584429956766479204505770141239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v193 ∧ v193 ≤ (538845790736945373031612642022758831348996103/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH3 hv192 (by norm_num) (by norm_num)
  have eR001 : (carryPairingRemainder carryMaterialEvenPairing 0 0 1) = v193 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193]
    change carryMaterialEvenPairing 0 1 = _
    rw [material_even_pairing_source]
    ring
  have hR001 : (4310766325895558584429956766479204505770141239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 0 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 0 1) ≤ (538845790736945373031612642022758831348996103/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR001]
    exact hv193
  let v194 : ℝ := (h 1)*(h 3)
  have hv194 : (6161652740870869901109050406370817322683/250000000000000000000000000000000000000000000000000000:ℝ) ≤ v194 ∧ v194 ≤ (61616527408708738659785381226583226577909/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hH3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v196 : ℝ := v194*(1/((h 0)))
  have hv196 : (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v196 ∧ v196 ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv194 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v195 : ℝ := v194/(h 0)
  have hv195 : (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v195 ∧ v195 ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v194/(h 0) ∧ v194/(h 0) ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv196
    change (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v194*(1/(h 0)) ∧ v194*(1/(h 0)) ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v197 : ℝ := (-1/1:ℝ)*v195
  have hv197 : (-2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v197 ∧ v197 ≤ (-2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv195 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v198 : ℝ := (h 4)+v197
  have hv198 : (10734709347019458596878677839067687880481323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v198 ∧ v198 ≤ (21469418694039077243916273587563321746201517/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH4 hv197 (by norm_num) (by norm_num)
  have eR002 : (carryPairingRemainder carryMaterialEvenPairing 0 0 2) = v198 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198]
    change carryMaterialEvenPairing 0 2 = _
    rw [material_even_pairing_source]
    ring
  have hR002 : (10734709347019458596878677839067687880481323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 0 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 0 2) ≤ (21469418694039077243916273587563321746201517/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR002]
    exact hv198
  let v199 : ℝ := (h 1)*(h 4)
  have hv199 : (597301248541535994162310383524206465209/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v199 ∧ v199 ≤ (1194602497083077686509197004889772644979/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hH4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v201 : ℝ := v199*(1/((h 0)))
  have hv201 : (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v201 ∧ v201 ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv199 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v200 : ℝ := v199/(h 0)
  have hv200 : (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v200 ∧ v200 ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v199/(h 0) ∧ v199/(h 0) ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv201
    change (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v199*(1/(h 0)) ∧ v199*(1/(h 0)) ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v202 : ℝ := (-1/1:ℝ)*v200
  have hv202 : (-51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v202 ∧ v202 ≤ (-25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv200 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v203 : ℝ := (h 5)+v202
  have hv203 : (418227058982069020711976915697378637819/39062500000000000000000000000000000000000000000000000:ℝ) ≤ v203 ∧ v203 ≤ (107066127099415001832233103572753462258223/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH5 hv202 (by norm_num) (by norm_num)
  have eR003 : (carryPairingRemainder carryMaterialEvenPairing 0 0 3) = v203 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203]
    change carryMaterialEvenPairing 0 3 = _
    rw [material_even_pairing_source]
    ring
  have hR003 : (418227058982069020711976915697378637819/39062500000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 0 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 0 3) ≤ (107066127099415001832233103572753462258223/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR003]
    exact hv203
  let v204 : ℝ := (h 2)*(h 1)
  have hv204 : (53593197793503399240255234436363802015604119/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v204 ∧ v204 ≤ (26796598896751701408468503234564610442009439/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hH1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v206 : ℝ := v204*(1/((h 0)))
  have hv206 : (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v206 ∧ v206 ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv204 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v205 : ℝ := v204/(h 0)
  have hv205 : (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v205 ∧ v205 ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v204/(h 0) ∧ v204/(h 0) ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv206
    change (92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v204*(1/(h 0)) ∧ v204*(1/(h 0)) ≤ (2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v207 : ℝ := (-1/1:ℝ)*v205
  have hv207 : (-2319550476634348000522642246985714465118642151/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v207 ∧ v207 ≤ (-92782019065373913825768502320556409138189507/400000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv205 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v208 : ℝ := (h 3)+v207
  have hv208 : (4310766325895558584429956766479204505770141239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v208 ∧ v208 ≤ (538845790736945373031612642022758831348996103/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH3 hv207 (by norm_num) (by norm_num)
  have eR010 : (carryPairingRemainder carryMaterialEvenPairing 0 1 0) = v208 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208]
    change carryMaterialEvenPairing 1 0 = _
    rw [material_even_pairing_source]
    ring
  have hR010 : (4310766325895558584429956766479204505770141239/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 1 0) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 1 0) ≤ (538845790736945373031612642022758831348996103/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR010]
    exact hv208
  let v209 : ℝ := (h 2)*(h 2)
  have hv209 : (12991326559757842362881125242403995965917/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v209 ∧ v209 ≤ (103930612478062752101226707642937360831481/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hH2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v211 : ℝ := v209*(1/((h 0)))
  have hv211 : (4498188420091123206120996607557192843992561/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v211 ∧ v211 ≤ (8996376840182247554993766821297144779496411/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv209 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v210 : ℝ := v209/(h 0)
  have hv210 : (4498188420091123206120996607557192843992561/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v210 ∧ v210 ≤ (8996376840182247554993766821297144779496411/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (4498188420091123206120996607557192843992561/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v209/(h 0) ∧ v209/(h 0) ≤ (8996376840182247554993766821297144779496411/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv211
    change (4498188420091123206120996607557192843992561/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v209*(1/(h 0)) ∧ v209*(1/(h 0)) ≤ (8996376840182247554993766821297144779496411/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v212 : ℝ := (-1/1:ℝ)*v210
  have hv212 : (-8996376840182247554993766821297144779496411/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v212 ∧ v212 ≤ (-4498188420091123206120996607557192843992561/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv210 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v213 : ℝ := (h 4)+v212
  have hv213 : (1157013233299184404639120335227649124767059/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v213 ∧ v213 ≤ (23140264665983842421246970934699592986953423/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH4 hv212 (by norm_num) (by norm_num)
  have eR011 : (carryPairingRemainder carryMaterialEvenPairing 0 1 1) = v213 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213]
    change carryMaterialEvenPairing 1 1 = _
    rw [material_even_pairing_source]
    ring
  have hR011 : (1157013233299184404639120335227649124767059/500000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 1 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 1 1) ≤ (23140264665983842421246970934699592986953423/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR011]
    exact hv213
  let v214 : ℝ := (h 2)*(h 3)
  have hv214 : (238979709963666805316299707419215035789/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v214 ∧ v214 ≤ (477959419927333946985869618677092917341/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hH3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v216 : ℝ := v214*(1/((h 0)))
  have hv216 : (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v216 ∧ v216 ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv214 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v215 : ℝ := v214/(h 0)
  have hv215 : (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v215 ∧ v215 ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v214/(h 0) ∧ v214/(h 0) ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv216
    change (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v214*(1/(h 0)) ∧ v214*(1/(h 0)) ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v217 : ℝ := (-1/1:ℝ)*v215
  have hv217 : (-41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v217 ∧ v217 ≤ (-41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv215 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v218 : ℝ := (h 5)+v217
  have hv218 : (58698260008238418154229657670086845904457/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v218 ∧ v218 ≤ (58698260008240975665967647724741948468711/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH5 hv217 (by norm_num) (by norm_num)
  have eR012 : (carryPairingRemainder carryMaterialEvenPairing 0 1 2) = v218 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218]
    change carryMaterialEvenPairing 1 2 = _
    rw [material_even_pairing_source]
    ring
  have hR012 : (58698260008238418154229657670086845904457/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 1 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 1 2) ≤ (58698260008240975665967647724741948468711/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR012]
    exact hv218
  let v219 : ℝ := (h 2)*(h 4)
  have hv219 : (2316632973983819039464421478688404097/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v219 ∧ v219 ≤ (4633265947967660458505163286097780667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hH4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v221 : ℝ := v219*(1/((h 0)))
  have hv221 : (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v221 ∧ v221 ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv219 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v220 : ℝ := v219/(h 0)
  have hv220 : (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v220 ∧ v220 ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v219/(h 0) ∧ v219/(h 0) ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv221
    change (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v219*(1/(h 0)) ∧ v219*(1/(h 0)) ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v222 : ℝ := (-1/1:ℝ)*v220
  have hv222 : (-100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v222 ∧ v222 ≤ (-200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv220 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v223 : ℝ := (h 6)+v222
  have hv223 : (589801634142779337492341456709190150751/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v223 ∧ v223 ≤ (294900817071473150638987258173750441243/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH6 hv222 (by norm_num) (by norm_num)
  have eR013 : (carryPairingRemainder carryMaterialEvenPairing 0 1 3) = v223 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223]
    change carryMaterialEvenPairing 1 3 = _
    rw [material_even_pairing_source]
    ring
  have hR013 : (589801634142779337492341456709190150751/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 1 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 1 3) ≤ (294900817071473150638987258173750441243/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR013]
    exact hv223
  let v224 : ℝ := (h 3)*(h 1)
  have hv224 : (6161652740870869901109050406370817322683/250000000000000000000000000000000000000000000000000000:ℝ) ≤ v224 ∧ v224 ≤ (61616527408708738659785381226583226577909/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hH1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v226 : ℝ := v224*(1/((h 0)))
  have hv226 : (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v226 ∧ v226 ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv224 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v225 : ℝ := v224/(h 0)
  have hv225 : (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v225 ∧ v225 ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v224/(h 0) ∧ v224/(h 0) ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv226
    change (2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v224*(1/(h 0)) ∧ v224*(1/(h 0)) ≤ (2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v227 : ℝ := (-1/1:ℝ)*v225
  have hv227 : (-2133444562425403690803763569542950302774989/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v227 ∧ v227 ≤ (-2666805703031752897393172640562664232184257/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv225 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v228 : ℝ := (h 4)+v227
  have hv228 : (10734709347019458596878677839067687880481323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v228 ∧ v228 ≤ (21469418694039077243916273587563321746201517/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH4 hv227 (by norm_num) (by norm_num)
  have eR020 : (carryPairingRemainder carryMaterialEvenPairing 0 2 0) = v228 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228]
    change carryMaterialEvenPairing 2 0 = _
    rw [material_even_pairing_source]
    ring
  have hR020 : (10734709347019458596878677839067687880481323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 2 0) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 2 0) ≤ (21469418694039077243916273587563321746201517/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR020]
    exact hv228
  let v229 : ℝ := (h 3)*(h 2)
  have hv229 : (238979709963666805316299707419215035789/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v229 ∧ v229 ≤ (477959419927333946985869618677092917341/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hH2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v231 : ℝ := v229*(1/((h 0)))
  have hv231 : (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v231 ∧ v231 ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv229 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v230 : ℝ := v229/(h 0)
  have hv230 : (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v230 ∧ v230 ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v229/(h 0) ∧ v229/(h 0) ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv231
    change (41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v229*(1/(h 0)) ∧ v229*(1/(h 0)) ≤ (41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v232 : ℝ := (-1/1:ℝ)*v230
  have hv232 : (-41372825132622156542033187690978677762667/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v232 ∧ v232 ≤ (-41372825132622127425454591885004251128267/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv230 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v233 : ℝ := (h 5)+v232
  have hv233 : (58698260008238418154229657670086845904457/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v233 ∧ v233 ≤ (58698260008240975665967647724741948468711/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH5 hv232 (by norm_num) (by norm_num)
  have eR021 : (carryPairingRemainder carryMaterialEvenPairing 0 2 1) = v233 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233]
    change carryMaterialEvenPairing 2 1 = _
    rw [material_even_pairing_source]
    ring
  have hR021 : (58698260008238418154229657670086845904457/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 2 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 2 1) ≤ (58698260008240975665967647724741948468711/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR021]
    exact hv233
  let v234 : ℝ := (h 3)*(h 3)
  have hv234 : (4396110090191040427168411621386627901/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v234 ∧ v234 ≤ (2198055045095523028116899960175302579/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hH3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v236 : ℝ := v234*(1/((h 0)))
  have hv236 : (190266669556258132234357861116715788061/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v236 ∧ v236 ≤ (47566667389064593967628021936091316201/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv234 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v235 : ℝ := v234/(h 0)
  have hv235 : (190266669556258132234357861116715788061/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v235 ∧ v235 ≤ (47566667389064593967628021936091316201/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    change (190266669556258132234357861116715788061/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v234/(h 0) ∧ v234/(h 0) ≤ (47566667389064593967628021936091316201/2500000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv236
    change (190266669556258132234357861116715788061/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v234*(1/(h 0)) ∧ v234*(1/(h 0)) ≤ (47566667389064593967628021936091316201/2500000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v237 : ℝ := (-1/1:ℝ)*v235
  have hv237 : (-47566667389064593967628021936091316201/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v237 ∧ v237 ≤ (-190266669556258132234357861116715788061/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv235 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v238 : ℝ := (h 6)+v237
  have hv238 : (120013180569666484345476146676269815961/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v238 ∧ v238 ≤ (150016475712124665134758378112223146429/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH6 hv237 (by norm_num) (by norm_num)
  have eR022 : (carryPairingRemainder carryMaterialEvenPairing 0 2 2) = v238 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238]
    change carryMaterialEvenPairing 2 2 = _
    rw [material_even_pairing_source]
    ring
  have hR022 : (120013180569666484345476146676269815961/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 2 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 2 2) ≤ (150016475712124665134758378112223146429/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR022]
    exact hv238
  let v239 : ℝ := (h 3)*(h 4)
  have hv239 : (21307611415521200767787945615483801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v239 ∧ v239 ≤ (133172571347008224853715600756361/62500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hH4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v241 : ℝ := v239*(1/((h 0)))
  have hv241 : (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v241 ∧ v241 ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv239 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v240 : ℝ := v239/(h 0)
  have hv240 : (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v240 ∧ v240 ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v239/(h 0) ∧ v239/(h 0) ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv241
    change (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v239*(1/(h 0)) ∧ v239*(1/(h 0)) ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v242 : ℝ := (-1/1:ℝ)*v240
  have hv242 : (-461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v242 ∧ v242 ≤ (-184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv240 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v243 : ℝ := (h 7)+v242
  have hv243 : (1512131658350428136123320455756651219/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v243 ∧ v243 ≤ (3024263316706268325137731711287816799/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH7 hv242 (by norm_num) (by norm_num)
  have eR023 : (carryPairingRemainder carryMaterialEvenPairing 0 2 3) = v243 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243]
    change carryMaterialEvenPairing 2 3 = _
    rw [material_even_pairing_source]
    ring
  have hR023 : (1512131658350428136123320455756651219/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 2 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 2 3) ≤ (3024263316706268325137731711287816799/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR023]
    exact hv243
  let v244 : ℝ := (h 4)*(h 1)
  have hv244 : (597301248541535994162310383524206465209/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v244 ∧ v244 ≤ (1194602497083077686509197004889772644979/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hH1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v246 : ℝ := v244*(1/((h 0)))
  have hv246 : (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v246 ∧ v246 ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv244 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v245 : ℝ := v244/(h 0)
  have hv245 : (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v245 ∧ v245 ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v244/(h 0) ∧ v244/(h 0) ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv246
    change (25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v244*(1/(h 0)) ∧ v244*(1/(h 0)) ≤ (51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v247 : ℝ := (-1/1:ℝ)*v245
  have hv247 : (-51703218049689323548226412612623438289917/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v247 ∧ v247 ≤ (-25851609024844538462578391880867342903733/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv245 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v248 : ℝ := (h 5)+v247
  have hv248 : (418227058982069020711976915697378637819/39062500000000000000000000000000000000000000000000000:ℝ) ≤ v248 ∧ v248 ≤ (107066127099415001832233103572753462258223/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH5 hv247 (by norm_num) (by norm_num)
  have eR030 : (carryPairingRemainder carryMaterialEvenPairing 0 3 0) = v248 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248]
    change carryMaterialEvenPairing 3 0 = _
    rw [material_even_pairing_source]
    ring
  have hR030 : (418227058982069020711976915697378637819/39062500000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 3 0) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 3 0) ≤ (107066127099415001832233103572753462258223/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR030]
    exact hv248
  let v249 : ℝ := (h 4)*(h 2)
  have hv249 : (2316632973983819039464421478688404097/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v249 ∧ v249 ≤ (4633265947967660458505163286097780667/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hH2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v251 : ℝ := v249*(1/((h 0)))
  have hv251 : (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v251 ∧ v251 ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv249 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v250 : ℝ := v249/(h 0)
  have hv250 : (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v250 ∧ v250 ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v249/(h 0) ∧ v249/(h 0) ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv251
    change (200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v249*(1/(h 0)) ∧ v249*(1/(h 0)) ≤ (100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v252 : ℝ := (-1/1:ℝ)*v250
  have hv252 : (-100265469130905730052775682208262096929/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v252 ∧ v252 ≤ (-200530938261810491495416857218107491291/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv250 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v253 : ℝ := (h 6)+v252
  have hv253 : (589801634142779337492341456709190150751/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v253 ∧ v253 ≤ (294900817071473150638987258173750441243/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH6 hv252 (by norm_num) (by norm_num)
  have eR031 : (carryPairingRemainder carryMaterialEvenPairing 0 3 1) = v253 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253]
    change carryMaterialEvenPairing 3 1 = _
    rw [material_even_pairing_source]
    ring
  have hR031 : (589801634142779337492341456709190150751/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 3 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 3 1) ≤ (294900817071473150638987258173750441243/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR031]
    exact hv253
  let v254 : ℝ := (h 4)*(h 3)
  have hv254 : (21307611415521200767787945615483801/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v254 ∧ v254 ≤ (133172571347008224853715600756361/62500000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hH3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v256 : ℝ := v254*(1/((h 0)))
  have hv256 : (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v256 ∧ v256 ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv254 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v255 : ℝ := v254/(h 0)
  have hv255 : (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v255 ∧ v255 ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v254/(h 0) ∧ v254/(h 0) ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv256
    change (184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v254*(1/(h 0)) ∧ v254*(1/(h 0)) ≤ (461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v257 : ℝ := (-1/1:ℝ)*v255
  have hv257 : (-461104041647643177163983502975296791/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v257 ∧ v257 ≤ (-184441616659056273596172265774981577/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv255 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v258 : ℝ := (h 7)+v257
  have hv258 : (1512131658350428136123320455756651219/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v258 ∧ v258 ≤ (3024263316706268325137731711287816799/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH7 hv257 (by norm_num) (by norm_num)
  have eR032 : (carryPairingRemainder carryMaterialEvenPairing 0 3 2) = v258 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258]
    change carryMaterialEvenPairing 3 2 = _
    rw [material_even_pairing_source]
    ring
  have hR032 : (1512131658350428136123320455756651219/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 3 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 3 2) ≤ (3024263316706268325137731711287816799/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR032]
    exact hv258
  let v259 : ℝ := (h 4)*(h 4)
  have hv259 : (103276372729582717688732508409659/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v259 ∧ v259 ≤ (103276372729583702263599672168033/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hH4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v261 : ℝ := v259*(1/((h 0)))
  have hv261 : (223493623680549561787163958815847/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v261 ∧ v261 ≤ (558734059201379231121215424816533/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv259 (show (432806880748497749965119234052470886097041698045697139521/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((h 0)) ∧ 1/((h 0)) ≤ (108201720187124437494880152110737888513177775804273999063/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hH0 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v260 : ℝ := v259/(h 0)
  have hv260 : (223493623680549561787163958815847/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v260 ∧ v260 ≤ (558734059201379231121215424816533/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    change (223493623680549561787163958815847/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v259/(h 0) ∧ v259/(h 0) ≤ (558734059201379231121215424816533/1250000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv261
    change (223493623680549561787163958815847/500000000000000000000000000000000000000000000000000000:ℝ) ≤ v259*(1/(h 0)) ∧ v259*(1/(h 0)) ≤ (558734059201379231121215424816533/1250000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v262 : ℝ := (-1/1:ℝ)*v260
  have hv262 : (-558734059201379231121215424816533/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v262 ∧ v262 ≤ (-223493623680549561787163958815847/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv260 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v263 : ℝ := (h 8)+v262
  have hv263 : (381569456593764646731402927145977/250000000000000000000000000000000000000000000000000000:ℝ) ≤ v263 ∧ v263 ≤ (15262778263926734878082643798644621/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hH8 hv262 (by norm_num) (by norm_num)
  have eR033 : (carryPairingRemainder carryMaterialEvenPairing 0 3 3) = v263 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263]
    change carryMaterialEvenPairing 3 3 = _
    rw [material_even_pairing_source]
    ring
  have hR033 : (381569456593764646731402927145977/250000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 0 3 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 0 3 3) ≤ (15262778263926734878082643798644621/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR033]
    exact hv263
  let v264 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 3)
  have hv264 : (1146315557206694556697112759/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v264 ∧ v264 ≤ (286578889301702185840838673/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR030 hR003 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v266 : ℝ := v264*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv266 : (1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v266 ∧ v266 ≤ (1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv264 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v265 : ℝ := v264/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv265 : (1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v265 ∧ v265 ≤ (1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v264/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v264/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv266
    change (1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v264*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v264*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v267 : ℝ := (0/1:ℝ)+v265
  have hv267 : (1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v267 ∧ v267 ≤ (1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv265 (by norm_num) (by norm_num)
  let v268 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 1)
  have hv268 : (1858270631647509320145267907843507519/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v268 ∧ v268 ≤ (1858270631647513113466985606157978051/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR010 hR001 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v270 : ℝ := v268*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv270 : (11012811530743476335052387692384478920937729/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v270 ∧ v270 ≤ (1376601441342937507690741747113515717624539/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv268 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v269 : ℝ := v268/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv269 : (11012811530743476335052387692384478920937729/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v269 ∧ v269 ≤ (1376601441342937507690741747113515717624539/625000000000000000000000000000000000000000000000000000:ℝ) := by
    change (11012811530743476335052387692384478920937729/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v268/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v268/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (1376601441342937507690741747113515717624539/625000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv270
    change (11012811530743476335052387692384478920937729/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v268*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v268*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (1376601441342937507690741747113515717624539/625000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v271 : ℝ := (-1/1:ℝ)*v269
  have hv271 : (-1376601441342937507690741747113515717624539/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v271 ∧ v271 ≤ (-11012811530743476335052387692384478920937729/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv269 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v272 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 1)+v271
  have hv272 : (278660401124171992432634687684182753337139/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v272 ∧ v272 ≤ (222928320899377950228439109986127029015593/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR011 hv271 (by norm_num) (by norm_num)
  have eR111 : (carryPairingRemainder carryMaterialEvenPairing 1 1 1) = v272 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272]
    change carryPairingRemainder carryMaterialEvenPairing 0 1 1-carryPairingRemainder carryMaterialEvenPairing 0 1 0*carryPairingRemainder carryMaterialEvenPairing 0 0 1/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR111 : (278660401124171992432634687684182753337139/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 1 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 1 1) ≤ (222928320899377950228439109986127029015593/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR111]
    exact hv272
  let v273 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 2)
  have hv273 : (4627482357140778234624012642058263/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v273 ∧ v273 ≤ (4627482357140817454647837135540707/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR010 hR002 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v275 : ℝ := v273*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv275 : (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v275 ∧ v275 ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv273 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v274 : ℝ := v273/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv274 : (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v274 ∧ v274 ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) := by
    change (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v273/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v273/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv275
    change (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v273*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v273*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v276 : ℝ := (-1/1:ℝ)*v274
  have hv276 : (-548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) ≤ v276 ∧ v276 ≤ (-21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv274 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v277 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 2)+v276
  have hv277 : (3849853976173248378478766368288891421157/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v277 ∧ v277 ≤ (7699707952352553920369424517773079521037/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR012 hv276 (by norm_num) (by norm_num)
  have eR112 : (carryPairingRemainder carryMaterialEvenPairing 1 1 2) = v277 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277]
    change carryPairingRemainder carryMaterialEvenPairing 0 1 2-carryPairingRemainder carryMaterialEvenPairing 0 1 0*carryPairingRemainder carryMaterialEvenPairing 0 0 2/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR112 : (3849853976173248378478766368288891421157/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 1 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 1 2) ≤ (7699707952352553920369424517773079521037/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR112]
    exact hv277
  let v278 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 3)
  have hv278 : (9230741106883782380662801304979/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v278 ∧ v278 ≤ (2884606595901328608723476695731/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR010 hR003 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v280 : ℝ := v278*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv280 : (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v280 ∧ v280 ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv278 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v279 : ℝ := v278/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv279 : (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v279 ∧ v279 ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v278/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v278/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv280
    change (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v278*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v278*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v281 : ℝ := (-1/1:ℝ)*v279
  have hv281 : (-109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v281 ∧ v281 ≤ (-109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv279 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v282 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 1 3)+v281
  have hv282 : (10688289003789045358036477764871177299/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v282 ∧ v282 ≤ (42753156015351011720566376014234084321/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR013 hv281 (by norm_num) (by norm_num)
  have eR113 : (carryPairingRemainder carryMaterialEvenPairing 1 1 3) = v282 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282]
    change carryPairingRemainder carryMaterialEvenPairing 0 1 3-carryPairingRemainder carryMaterialEvenPairing 0 1 0*carryPairingRemainder carryMaterialEvenPairing 0 0 3/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR113 : (10688289003789045358036477764871177299/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 1 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 1 3) ≤ (42753156015351011720566376014234084321/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR113]
    exact hv282
  let v283 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 1)
  have hv283 : (4627482357140778234624012642058263/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v283 ∧ v283 ≤ (4627482357140817454647837135540707/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR020 hR001 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v285 : ℝ := v283*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv285 : (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v285 ∧ v285 ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv283 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v284 : ℝ := v283/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv284 : (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v284 ∧ v284 ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) := by
    change (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v283/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v283/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv285
    change (21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v283*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v283*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v286 : ℝ := (-1/1:ℝ)*v284
  have hv286 : (-548484060320651697757508913017979544833/50000000000000000000000000000000000000000000000000000:ℝ) ≤ v286 ∧ v286 ≤ (-21939362412825879482313174186342163483277/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv284 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v287 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 1)+v286
  have hv287 : (3849853976173248378478766368288891421157/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v287 ∧ v287 ≤ (7699707952352553920369424517773079521037/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR021 hv286 (by norm_num) (by norm_num)
  have eR121 : (carryPairingRemainder carryMaterialEvenPairing 1 2 1) = v287 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287]
    change carryPairingRemainder carryMaterialEvenPairing 0 2 1-carryPairingRemainder carryMaterialEvenPairing 0 2 0*carryPairingRemainder carryMaterialEvenPairing 0 0 1/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR121 : (3849853976173248378478766368288891421157/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 2 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 2 1) ≤ (7699707952352553920369424517773079521037/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR121]
    exact hv287
  let v288 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 2)
  have hv288 : (4609359390599477246903458987403/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v288 ∧ v288 ≤ (4609359390599545970580936108943/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR020 hR002 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v290 : ℝ := v288*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv290 : (109267197967025856732450179678230476347/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v290 ∧ v290 ≤ (273167994917568745557082498486119050503/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv288 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v289 : ℝ := v288/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv289 : (109267197967025856732450179678230476347/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v289 ∧ v289 ≤ (273167994917568745557082498486119050503/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (109267197967025856732450179678230476347/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v288/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v288/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (273167994917568745557082498486119050503/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv290
    change (109267197967025856732450179678230476347/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v288*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v288*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (273167994917568745557082498486119050503/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v291 : ℝ := (-1/1:ℝ)*v289
  have hv291 : (-273167994917568745557082498486119050503/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v291 ∧ v291 ≤ (-109267197967025856732450179678230476347/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv289 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v292 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 2)+v291
  have hv292 : (53729913013194930613215736409110978799/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v292 ∧ v292 ≤ (53729913013369376876782614057740203981/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR022 hv291 (by norm_num) (by norm_num)
  have eR122 : (carryPairingRemainder carryMaterialEvenPairing 1 2 2) = v292 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292]
    change carryPairingRemainder carryMaterialEvenPairing 0 2 2-carryPairingRemainder carryMaterialEvenPairing 0 2 0*carryPairingRemainder carryMaterialEvenPairing 0 0 2/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR122 : (53729913013194930613215736409110978799/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 2 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 2 2) ≤ (53729913013369376876782614057740203981/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR122]
    exact hv292
  let v293 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 3)
  have hv293 : (229864751064641266369560693377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v293 ∧ v293 ≤ (114932375532327214298241211759/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR020 hR003 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v295 : ℝ := v293*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv295 : (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v295 ∧ v295 ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv293 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v294 : ℝ := v293/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv294 : (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v294 ∧ v294 ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) := by
    change (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v293/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v293/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv295
    change (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v293*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v293*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v296 : ℝ := (-1/1:ℝ)*v294
  have hv296 : (-54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) ≤ v296 ∧ v296 ≤ (-6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv294 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v297 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 2 3)+v296
  have hv297 : (9366661471351252561403237687927559/312500000000000000000000000000000000000000000000000000:ℝ) ≤ v297 ∧ v297 ≤ (299733167088808451694007338075280399/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR023 hv296 (by norm_num) (by norm_num)
  have eR123 : (carryPairingRemainder carryMaterialEvenPairing 1 2 3) = v297 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297]
    change carryPairingRemainder carryMaterialEvenPairing 0 2 3-carryPairingRemainder carryMaterialEvenPairing 0 2 0*carryPairingRemainder carryMaterialEvenPairing 0 0 3/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR123 : (9366661471351252561403237687927559/312500000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 2 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 2 3) ≤ (299733167088808451694007338075280399/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR123]
    exact hv297
  let v298 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 1)
  have hv298 : (9230741106883782380662801304979/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v298 ∧ v298 ≤ (2884606595901328608723476695731/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR030 hR001 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v300 : ℝ := v298*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv300 : (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v300 ∧ v300 ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv298 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v299 : ℝ := v298/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv299 : (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v299 ∧ v299 ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v298/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v298/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv300
    change (109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v298*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v298*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v301 : ℝ := (-1/1:ℝ)*v299
  have hv301 : (-109409695625524631212039109129941088311/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ v301 ∧ v301 ≤ (-109409695625519057911481628066653359633/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv299 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v302 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 1)+v301
  have hv302 : (10688289003789045358036477764871177299/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v302 ∧ v302 ≤ (42753156015351011720566376014234084321/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR031 hv301 (by norm_num) (by norm_num)
  have eR131 : (carryPairingRemainder carryMaterialEvenPairing 1 3 1) = v302 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302]
    change carryPairingRemainder carryMaterialEvenPairing 0 3 1-carryPairingRemainder carryMaterialEvenPairing 0 3 0*carryPairingRemainder carryMaterialEvenPairing 0 0 1/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR131 : (10688289003789045358036477764871177299/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 3 1) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 3 1) ≤ (42753156015351011720566376014234084321/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR131]
    exact hv302
  let v303 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 0)*(carryPairingRemainder carryMaterialEvenPairing 0 0 2)
  have hv303 : (229864751064641266369560693377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v303 ∧ v303 ≤ (114932375532327214298241211759/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR030 hR002 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v305 : ℝ := v303*(1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)))
  have hv305 : (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v305 ∧ v305 ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv303 (show (29631882846309947067566585515508260807273284243735289355358509/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (59263765692619900839326724044687874733753818706606039178583311/5000000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR000 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v304 : ℝ := v303/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)
  have hv304 : (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v304 ∧ v304 ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) := by
    change (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v303/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ∧ v303/(carryPairingRemainder carryMaterialEvenPairing 0 0 0) ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv305
    change (6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) ≤ v303*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ∧ v303*(1/(carryPairingRemainder carryMaterialEvenPairing 0 0 0)) ≤ (54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v306 : ℝ := (-1/1:ℝ)*v304
  have hv306 : (-54490602992352323805634746109992411/200000000000000000000000000000000000000000000000000000:ℝ) ≤ v306 ∧ v306 ≤ (-6811325374043649683609310933031341/25000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv304 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v307 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 2)+v306
  have hv307 : (9366661471351252561403237687927559/312500000000000000000000000000000000000000000000000000:ℝ) ≤ v307 ∧ v307 ≤ (299733167088808451694007338075280399/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR032 hv306 (by norm_num) (by norm_num)
  have eR132 : (carryPairingRemainder carryMaterialEvenPairing 1 3 2) = v307 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307]
    change carryPairingRemainder carryMaterialEvenPairing 0 3 2-carryPairingRemainder carryMaterialEvenPairing 0 3 0*carryPairingRemainder carryMaterialEvenPairing 0 0 2/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR132 : (9366661471351252561403237687927559/312500000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 3 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 3 2) ≤ (299733167088808451694007338075280399/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR132]
    exact hv307
  let v308 : ℝ := (-1/1:ℝ)*v265
  have hv308 : (-1358699531842186746595771891552791/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v308 ∧ v308 ≤ (-1698374414802564062820846073133403/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv265 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v309 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 0 3 3)+v308
  have hv309 : (167578294532871840329839817031117/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v309 ∧ v309 ≤ (1675782945506222375515875213577397/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR033 hv308 (by norm_num) (by norm_num)
  have eR133 : (carryPairingRemainder carryMaterialEvenPairing 1 3 3) = v309 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309]
    change carryPairingRemainder carryMaterialEvenPairing 0 3 3-carryPairingRemainder carryMaterialEvenPairing 0 3 0*carryPairingRemainder carryMaterialEvenPairing 0 0 3/carryPairingRemainder carryMaterialEvenPairing 0 0 0 = _
    ring
  have hR133 : (167578294532871840329839817031117/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 1 3 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 1 3 3) ≤ (1675782945506222375515875213577397/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR133]
    exact hv309
  let v310 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 3 1)*(carryPairingRemainder carryMaterialEvenPairing 1 1 3)
  have hv310 : (182783234925628517849/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v310 ∧ v310 ≤ (91391617463647219897/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR131 hR113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v312 : ℝ := v310*(1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)))
  have hv312 : (1639838618872749500605360362765289/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v312 ∧ v312 ≤ (204979827360999020681493474560981/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv310 (show (44857467905630753699645784062177977167406060474264719159438730013807/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (22428733952819437080107152263140425365511542313880539340436733302487/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR111 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v311 : ℝ := v310/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)
  have hv311 : (1639838618872749500605360362765289/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v311 ∧ v311 ≤ (204979827360999020681493474560981/1250000000000000000000000000000000000000000000000000000:ℝ) := by
    change (1639838618872749500605360362765289/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v310/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ∧ v310/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ≤ (204979827360999020681493474560981/1250000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv312
    change (1639838618872749500605360362765289/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v310*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ v310*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (204979827360999020681493474560981/1250000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v313 : ℝ := v267+v311
  have hv313 : (15226833937293262003172128947832513/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v313 ∧ v313 ≤ (7613416968654929815704833356007879/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv267 hv311 (by norm_num) (by norm_num)
  let v314 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 2 1)*(carryPairingRemainder carryMaterialEvenPairing 1 1 2)
  have hv314 : (5928550255142788197389631/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v314 ∧ v314 ≤ (1482137563788028968811969/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR121 hR112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v316 : ℝ := v314*(1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)))
  have hv316 : (26593975279698663776358544805756249963/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v316 ∧ v316 ≤ (53187950559490639266464238089080804499/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv314 (show (44857467905630753699645784062177977167406060474264719159438730013807/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (22428733952819437080107152263140425365511542313880539340436733302487/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR111 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v315 : ℝ := v314/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)
  have hv315 : (26593975279698663776358544805756249963/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v315 ∧ v315 ≤ (53187950559490639266464238089080804499/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (26593975279698663776358544805756249963/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v314/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ∧ v314/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ≤ (53187950559490639266464238089080804499/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv316
    change (26593975279698663776358544805756249963/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v314*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ v314*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (53187950559490639266464238089080804499/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v317 : ℝ := (-1/1:ℝ)*v315
  have hv317 : (-53187950559490639266464238089080804499/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v317 ∧ v317 ≤ (-26593975279698663776358544805756249963/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv315 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v318 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 2 2)+v317
  have hv318 : (5419624537042913467514983200301743/100000000000000000000000000000000000000000000000000000:ℝ) ≤ v318 ∧ v318 ≤ (108392490794409864813104889245540811/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR122 hv317 (by norm_num) (by norm_num)
  have eR222 : (carryPairingRemainder carryMaterialEvenPairing 2 2 2) = v318 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318]
    change carryPairingRemainder carryMaterialEvenPairing 1 2 2-carryPairingRemainder carryMaterialEvenPairing 1 2 1*carryPairingRemainder carryMaterialEvenPairing 1 1 2/carryPairingRemainder carryMaterialEvenPairing 1 1 1 = _
    ring
  have hR222 : (5419624537042913467514983200301743/100000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 2 2 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 2 2 2) ≤ (108392490794409864813104889245540811/2000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR222]
    exact hv318
  let v319 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 2 1)*(carryPairingRemainder carryMaterialEvenPairing 1 1 3)
  have hv319 : (32918681535780851260399/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v319 ∧ v319 ≤ (32918681535956761177747/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR121 hR113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v321 : ℝ := v319*(1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)))
  have hv321 : (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v321 ∧ v321 ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv319 (show (44857467905630753699645784062177977167406060474264719159438730013807/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (22428733952819437080107152263140425365511542313880539340436733302487/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR111 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v320 : ℝ := v319/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)
  have hv320 : (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v320 ∧ v320 ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v319/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ∧ v319/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv321
    change (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v319*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ v319*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v322 : ℝ := (-1/1:ℝ)*v320
  have hv322 : (-147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v322 ∧ v322 ≤ (-147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv320 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v323 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 2 3)+v322
  have hv323 : (2201713492107299680433546931226731/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v323 ∧ v323 ≤ (4403426991414606755390923542544357/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR123 hv322 (by norm_num) (by norm_num)
  have eR223 : (carryPairingRemainder carryMaterialEvenPairing 2 2 3) = v323 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323]
    change carryPairingRemainder carryMaterialEvenPairing 1 2 3-carryPairingRemainder carryMaterialEvenPairing 1 2 1*carryPairingRemainder carryMaterialEvenPairing 1 1 3/carryPairingRemainder carryMaterialEvenPairing 1 1 1 = _
    ring
  have hR223 : (2201713492107299680433546931226731/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 2 2 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 2 2 3) ≤ (4403426991414606755390923542544357/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR223]
    exact hv323
  let v324 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 3 1)*(carryPairingRemainder carryMaterialEvenPairing 1 1 2)
  have hv324 : (32918681535780851260399/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v324 ∧ v324 ≤ (32918681535956761177747/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR131 hR112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v326 : ℝ := v324*(1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)))
  have hv326 : (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v326 ∧ v326 ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv324 (show (44857467905630753699645784062177977167406060474264719159438730013807/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (22428733952819437080107152263140425365511542313880539340436733302487/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR111 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v325 : ℝ := v324/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)
  have hv325 : (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v325 ∧ v325 ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v324/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ∧ v324/(carryPairingRemainder carryMaterialEvenPairing 1 1 1) ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv326
    change (147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v324*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ∧ v324*(1/(carryPairingRemainder carryMaterialEvenPairing 1 1 1)) ≤ (147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v327 : ℝ := (-1/1:ℝ)*v325
  have hv327 : (-147664870049512741302018256075614213/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v327 ∧ v327 ≤ (-147664870048696922469308207266368021/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv325 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v328 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 3 2)+v327
  have hv328 : (2201713492107299680433546931226731/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v328 ∧ v328 ≤ (4403426991414606755390923542544357/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR132 hv327 (by norm_num) (by norm_num)
  have eR232 : (carryPairingRemainder carryMaterialEvenPairing 2 3 2) = v328 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328]
    change carryPairingRemainder carryMaterialEvenPairing 1 3 2-carryPairingRemainder carryMaterialEvenPairing 1 3 1*carryPairingRemainder carryMaterialEvenPairing 1 1 2/carryPairingRemainder carryMaterialEvenPairing 1 1 1 = _
    ring
  have hR232 : (2201713492107299680433546931226731/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 2 3 2) ∧ (carryPairingRemainder carryMaterialEvenPairing 2 3 2) ≤ (4403426991414606755390923542544357/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR232]
    exact hv328
  let v329 : ℝ := (-1/1:ℝ)*v311
  have hv329 : (-204979827360999020681493474560981/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v329 ∧ v329 ≤ (-1639838618872749500605360362765289/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv311 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v330 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 1 3 3)+v329
  have hv330 : (17972163220363118923225186911661/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v330 ∧ v330 ≤ (8986081658368218727628712703027/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR133 hv329 (by norm_num) (by norm_num)
  have eR233 : (carryPairingRemainder carryMaterialEvenPairing 2 3 3) = v330 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330]
    change carryPairingRemainder carryMaterialEvenPairing 1 3 3-carryPairingRemainder carryMaterialEvenPairing 1 3 1*carryPairingRemainder carryMaterialEvenPairing 1 1 3/carryPairingRemainder carryMaterialEvenPairing 1 1 1 = _
    ring
  have hR233 : (17972163220363118923225186911661/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 2 3 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 2 3 3) ≤ (8986081658368218727628712703027/2500000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR233]
    exact hv330
  let v331 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 2 3 2)*(carryPairingRemainder carryMaterialEvenPairing 2 2 3)
  have hv331 : (193901692053/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v331 ∧ v331 ≤ (242377115859/1250000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hR232 hR223 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v333 : ℝ := v331*(1/((carryPairingRemainder carryMaterialEvenPairing 2 2 2)))
  have hv333 : (35777698368566341410767197759377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v333 ∧ v333 ≤ (35777698503261583948637182308597/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv331 (show (36902925384258190159515242772720189368097319660755726416591795452817888493/2000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((carryPairingRemainder carryMaterialEvenPairing 2 2 2)) ∧ 1/((carryPairingRemainder carryMaterialEvenPairing 2 2 2)) ≤ (46128656753112722020085482312069672714368946765869186153632780800459061277/2500000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv hR222 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v332 : ℝ := v331/(carryPairingRemainder carryMaterialEvenPairing 2 2 2)
  have hv332 : (35777698368566341410767197759377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v332 ∧ v332 ≤ (35777698503261583948637182308597/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (35777698368566341410767197759377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v331/(carryPairingRemainder carryMaterialEvenPairing 2 2 2) ∧ v331/(carryPairingRemainder carryMaterialEvenPairing 2 2 2) ≤ (35777698503261583948637182308597/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv333
    change (35777698368566341410767197759377/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v331*(1/(carryPairingRemainder carryMaterialEvenPairing 2 2 2)) ∧ v331*(1/(carryPairingRemainder carryMaterialEvenPairing 2 2 2)) ≤ (35777698503261583948637182308597/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  let v334 : ℝ := v313+v332
  have hv334 : (1526261163566182834458289614559189/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v334 ∧ v334 ≤ (3052522327162624243071660778864871/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv313 hv332 (by norm_num) (by norm_num)
  let v335 : ℝ := (-1/1:ℝ)*v332
  have hv335 : (-35777698503261583948637182308597/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v335 ∧ v335 ≤ (-35777698368566341410767197759377/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv332 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v336 : ℝ := (carryPairingRemainder carryMaterialEvenPairing 2 3 3)+v335
  have hv336 : (6665117498586155912527660589/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v336 ∧ v336 ≤ (166628264906533499747653052731/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hR233 hv335 (by norm_num) (by norm_num)
  have eR333 : (carryPairingRemainder carryMaterialEvenPairing 3 3 3) = v336 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336]
    change carryPairingRemainder carryMaterialEvenPairing 2 3 3-carryPairingRemainder carryMaterialEvenPairing 2 3 2*carryPairingRemainder carryMaterialEvenPairing 2 2 3/carryPairingRemainder carryMaterialEvenPairing 2 2 2 = _
    ring
  have hR333 : (6665117498586155912527660589/400000000000000000000000000000000000000000000000000000:ℝ) ≤ (carryPairingRemainder carryMaterialEvenPairing 3 3 3) ∧ (carryPairingRemainder carryMaterialEvenPairing 3 3 3) ≤ (166628264906533499747653052731/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eR333]
    exact hv336
  let v337 : ℝ := v260+v334
  have hv337 : (1973248410927281958032617532190883/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ v337 ∧ v337 ≤ (19732484109424155064328027292856619/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv260 hv334 (by norm_num) (by norm_num)
  have eThreshold : carryMaterialFourthSourceThreshold = v337 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337]
    rw [material_fourth_threshold_eq]
    try dsimp only [carryMaterialFourthOldCoupling,carryPairingPivot,carryPairingRemainder]
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337]
    ring
  have hThreshold : (1973248410927281958032617532190883/1000000000000000000000000000000000000000000000000000000:ℝ) ≤ carryMaterialFourthSourceThreshold ∧ carryMaterialFourthSourceThreshold ≤ (19732484109424155064328027292856619/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eThreshold]
    exact hv337
  let v338 : ℝ := (h 0)*(c 8)
  have hv338 : (48515166961259469056819844350099363/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v338 ∧ v338 ≤ (2425758348062974035928047947255561/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH0 hC8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v339 : ℝ := (0/1:ℝ)+v338
  have hv339 : (48515166961259469056819844350099363/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v339 ∧ v339 ≤ (2425758348062974035928047947255561/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add (show (0/1:ℝ) ≤ (0/1:ℝ) ∧ (0/1:ℝ) ≤ (0/1:ℝ) from ⟨le_rfl,le_rfl⟩) hv338 (by norm_num) (by norm_num)
  let v340 : ℝ := (h 1)*(c 7)
  have hv340 : (-38323560108309900845264489816102911/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v340 ∧ v340 ≤ (-7664712021661979342916692757391383/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH1 hC7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v341 : ℝ := v339+v340
  have hv341 : (2547901713237392052888838633499113/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v341 ∧ v341 ≤ (2038321370589916800795499031630861/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv339 hv340 (by norm_num) (by norm_num)
  let v342 : ℝ := (h 2)*(c 6)
  have hv342 : (15406931082398556301910822147463763/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v342 ∧ v342 ≤ (6162772432959423167824585894102849/1000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH2 hC6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v343 : ℝ := v341+v342
  have hv343 : (4488708198908987088699915195240719/625000000000000000000000000000000000000000000000000000:ℝ) ≤ v343 ∧ v343 ≤ (14363866236508763136444670819836559/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv341 hv342 (by norm_num) (by norm_num)
  let v344 : ℝ := (h 3)*(c 5)
  have hv344 : (-48454440591736858119101992956409279/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v344 ∧ v344 ≤ (-96908881183473652777753813967274139/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH3 hC5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v345 : ℝ := v343+v344
  have hv345 : (-12544775000464961409502671394483527/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v345 ∧ v345 ≤ (-1568096875058114818470653741755709/625000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv343 hv344 (by norm_num) (by norm_num)
  let v346 : ℝ := (h 4)*(c 4)
  have hv346 : (1282967534919436912370208781084977/100000000000000000000000000000000000000000000000000000:ℝ) ≤ v346 ∧ v346 ≤ (2004636773311629739833626824895151/156250000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH4 hC4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v347 : ℝ := v345+v346
  have hv347 : (51603601745506884209007767659765323/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v347 ∧ v347 ≤ (1290090043637680828172770711564979/125000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv345 hv346 (by norm_num) (by norm_num)
  let v348 : ℝ := (h 5)*(c 3)
  have hv348 : (-264305069421694846039855277597543/20000000000000000000000000000000000000000000000000000:ℝ) ≤ v348 ∧ v348 ≤ (-6607626735542159480075187594148993/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH5 hC3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v349 : ℝ := v347+v348
  have hv349 : (-14472665609916827300956051739620427/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v349 ∧ v349 ≤ (-1447266560991436167384104747889077/500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv347 hv348 (by norm_num) (by norm_num)
  let v350 : ℝ := (h 6)*(c 2)
  have hv350 : (12196018876256557211368633813798071/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v350 ∧ v350 ≤ (19513630202014590029414286020247759/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH6 hC2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v351 : ℝ := v349+v350
  have hv351 : (34311409895109401544518483515571857/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v351 ∧ v351 ≤ (13724563958048845359877867028691451/2000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv349 hv350 (by norm_num) (by norm_num)
  let v352 : ℝ := (h 7)*(c 1)
  have hv352 : (-45329060621074827769498174052103139/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v352 ∧ v352 ≤ (-45329060621012722352220065862460827/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hH7 hC1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v353 : ℝ := v351+v352
  have hv353 : (931750366765759012781551719161623/400000000000000000000000000000000000000000000000000000:ℝ) ≤ v353 ∧ v353 ≤ (5823439792307876111792317320249107/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv351 hv352 (by norm_num) (by norm_num)
  let v354 : ℝ := (c 0)*carryMaterialFourthSourceThreshold
  have hv354 : (1226178481998780783178755693783317/1250000000000000000000000000000000000000000000000000000:ℝ) ≤ v354 ∧ v354 ≤ (4904713928032739139503200120495507/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hC0 hThreshold (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v355 : ℝ := v353+v354
  have hv355 : (33103187025134221584968838529307111/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v355 ∧ v355 ≤ (16551593512648491363087834760993721/5000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hv353 hv354 (by norm_num) (by norm_num)
  let v356 : ℝ := v355*(-1/1:ℝ)
  have hv356 : (-16551593512648491363087834760993721/5000000000000000000000000000000000000000000000000000000:ℝ) ≤ v356 ∧ v356 ≤ (-33103187025134221584968838529307111/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv355 (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v358 : ℝ := v356*(1/((9/1:ℝ)))
  have hv358 : (-919532972924916186838213042277429/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v358 ∧ v358 ≤ (-3678131891681580176107648725478567/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul hv356 (show (1111111111111111111111111111111111111111111111111111111/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1/((9/1:ℝ)) ∧ 1/((9/1:ℝ)) ≤ (138888888888888888888888888888888888888888888888888889/1250000000000000000000000000000000000000000000000000000:ℝ) from enclose_inv (show (9/1:ℝ) ≤ (9/1:ℝ) ∧ (9/1:ℝ) ≤ (9/1:ℝ) from ⟨le_rfl,le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v357 : ℝ := v356/(9/1:ℝ)
  have hv357 : (-919532972924916186838213042277429/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v357 ∧ v357 ≤ (-3678131891681580176107648725478567/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    change (-919532972924916186838213042277429/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v356/(9/1:ℝ) ∧ v356/(9/1:ℝ) ≤ (-3678131891681580176107648725478567/10000000000000000000000000000000000000000000000000000000:ℝ)
    have hprod := hv358
    change (-919532972924916186838213042277429/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ v356*(1/(9/1:ℝ)) ∧ v356*(1/(9/1:ℝ)) ≤ (-3678131891681580176107648725478567/10000000000000000000000000000000000000000000000000000000:ℝ) at hprod
    simpa only [div_eq_mul_inv,one_mul] using hprod
  have eCeiling : material_fourth_characteristic_ceiling = v357 := by
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358]
    rw [material_fourth_characteristic_ceiling]
    try dsimp only [v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358]
    norm_num [Finset.sum_range_succ]
  have hCeiling : (-919532972924916186838213042277429/2500000000000000000000000000000000000000000000000000000:ℝ) ≤ material_fourth_characteristic_ceiling ∧ material_fourth_characteristic_ceiling ≤ (-3678131891681580176107648725478567/10000000000000000000000000000000000000000000000000000000:ℝ) := by
    rw [eCeiling]
    exact hv357
  let v359 : ℝ := (-1/1:ℝ)*(c 9)
  have hv359 : (3678141095500769229851175712561149/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v359 ∧ v359 ≤ (919535273875192780262580786685767/2500000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_mul (show (-1/1:ℝ) ≤ (-1/1:ℝ) ∧ (-1/1:ℝ) ≤ (-1/1:ℝ) from ⟨le_rfl,le_rfl⟩) hC9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v360 : ℝ := material_fourth_characteristic_ceiling+v359
  have hv360 : (9203801104482498323543451433/10000000000000000000000000000000000000000000000000000000:ℝ) ≤ v360 ∧ v360 ≤ (9203819190944942674421264501/10000000000000000000000000000000000000000000000000000000:ℝ) :=
    enclose_add hCeiling hv359 (by norm_num) (by norm_num)
  change carryMaterialFourthPivot = _ at eR333
  have hp : (833/50000000000000000000000000000:ℝ) < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < (1667/100000000000000000000000000000:ℝ) := by
    change (833/50000000000000000000000000000:ℝ) < carryPairingRemainder carryMaterialEvenPairing 3 3 3 ∧ carryPairingRemainder carryMaterialEvenPairing 3 3 3 < (1667/100000000000000000000000000000:ℝ)
    constructor <;> linarith only [hR333.1,hR333.2]
  have hB : (-36781318917/100000000000000000000000000000000:ℝ) < material_fourth_characteristic_ceiling ∧ material_fourth_characteristic_ceiling < (-22988324323/62500000000000000000000000000000:ℝ) := by
    constructor <;> linarith only [hCeiling.1,hCeiling.2]
  have hgap : (9203/10000000000000000000000000000000:ℝ) < material_fourth_characteristic_ceiling-c 9 ∧ material_fourth_characteristic_ceiling-c 9 < (2301/2500000000000000000000000000000:ℝ) := by
    have egap : material_fourth_characteristic_ceiling-c 9 = v360 := by
      dsimp only [v360,v359]
      ring
    rw [egap]
    constructor <;> linarith only [hv360.1,hv360.2]
  exact ⟨hp,hB,hgap⟩

/-- The exact back-substituted material combination keeps a certified margin,
conditional on the displayed analytic source enclosure. -/
theorem material_fourth_critical_margin_of_theta_box (hb : material_fourth_theta_box) :
    (833/50000000000000000000000000000:ℝ) <
      carryPairingBilinear carryMaterialEvenPairing 4
        carryMaterialFourthCritical carryMaterialFourthCritical := by
  rw [material_fourth_critical_energy]
  exact (material_fourth_bounds_of_theta_box hb).1.1

theorem material_fourth_posDef_of_theta_box (hb : material_fourth_theta_box) :
    Matrix.PosDef (fun i j : Fin 4 => carryMaterialEvenPairing i j) := by
  apply material_fourth_block_posDef_iff.mpr
  exact lt_trans (by norm_num) (material_fourth_bounds_of_theta_box hb).1.1

theorem material_fourth_cholesky_of_theta_box (hb : material_fourth_theta_box) :
    carryMaterialEvenCholesky 4*(carryMaterialEvenCholesky 4)ᵀ =
      (fun i j : Fin 4 => carryMaterialEvenPairing i j) := by
  apply material_fourth_cholesky_of_source_estimate
  have he := (material_fourth_bounds_of_theta_box hb).2.2.1
  linarith only [he]

end
end CarryMaterialPivotCertificate

namespace CarryMaterialPivotCertificate
#assert_central_comparison_axioms enclose_add
#print axioms enclose_add
#assert_central_comparison_axioms enclose_neg
#print axioms enclose_neg
#assert_central_comparison_axioms enclose_mul
#print axioms enclose_mul
#assert_central_comparison_axioms enclose_inv
#print axioms enclose_inv
#assert_central_comparison_axioms material_fourth_theta_box_lower
#print axioms material_fourth_theta_box_lower
#assert_central_comparison_axioms material_fourth_theta_box_upper
#print axioms material_fourth_theta_box_upper
#assert_central_comparison_axioms material_fourth_theta_box
#print axioms material_fourth_theta_box
#assert_central_comparison_axioms material_fourth_bounds_of_theta_box
#print axioms material_fourth_bounds_of_theta_box
#assert_central_comparison_axioms material_fourth_critical_margin_of_theta_box
#print axioms material_fourth_critical_margin_of_theta_box
#assert_central_comparison_axioms material_fourth_posDef_of_theta_box
#print axioms material_fourth_posDef_of_theta_box
#assert_central_comparison_axioms material_fourth_cholesky_of_theta_box
#print axioms material_fourth_cholesky_of_theta_box
end CarryMaterialPivotCertificate
