import GeometryOfNumbers.Analysis.CarryMaterialNullHierarchy
import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Confluent scalar observations after complete material synthesis. Orders
are Taylor orders, never depth or camera. No positive carrier is constructed. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open Filter
open scoped Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def carryScalarJetShift (n : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (fun g : ℝ → ℂ => dslope g 0)^[n] f

theorem carryScalarJetShift_succ (n : ℕ) (f : ℝ → ℂ) :
    carryScalarJetShift (n+1) f = dslope (carryScalarJetShift n f) 0 :=
  Function.iterate_succ_apply' _ _ _

theorem carryScalarJetShift_add (p q : ℕ) (f : ℝ → ℂ) :
    carryScalarJetShift q (carryScalarJetShift p f) = carryScalarJetShift (p+q) f := by
  simpa only [carryScalarJetShift, Nat.add_comm] using
    (Function.iterate_add_apply (fun g : ℝ → ℂ => dslope g 0) q p f).symm

theorem carryScalarJetShift_analytic {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (n : ℕ) :
    AnalyticAt ℝ (carryScalarJetShift n f) 0 := by
  rcases hf with ⟨p,hp⟩
  exact (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt

theorem carryScalarJetShift_germ {f g : ℝ → ℂ} (h : f =ᶠ[nhds 0] g) (n : ℕ) :
    carryScalarJetShift n f =ᶠ[nhds 0] carryScalarJetShift n g := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [carryScalarJetShift_succ,carryScalarJetShift_succ]
    filter_upwards [ih] with t ht
    by_cases hz : t = 0
    · subst t; simp only [dslope_same]; exact ih.deriv_eq
    · simp only [dslope_of_ne _ hz, slope, Complex.real_smul, vsub_eq_sub]
      rw [ht, ih.eq_of_nhds]

theorem carryScalar_dslope_symm (f : ℝ → ℂ) (t u : ℝ) :
    dslope f t u = dslope f u t := by
  by_cases h : t = u
  · subst u; rfl
  · rw [dslope_of_ne _ (Ne.symm h),dslope_of_ne _ h]
    exact slope_comm f t u

private theorem row_germ (f : ℝ → ℂ) (u : ℝ) (hu : u ≠ 0) :
    (fun t => dslope f t u) =ᶠ[nhds 0]
      (fun t => (f u-f t)/((u-t : ℝ) : ℂ)) := by
  have hn : ∀ᶠ t : ℝ in nhds 0, u ≠ t := by
    exact (isOpen_ne_fun continuous_const continuous_id).mem_nhds hu
  filter_upwards [hn] with t ht
  simp only [dslope_of_ne _ ht,slope,Complex.real_smul,vsub_eq_sub,
    Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

theorem carryScalar_dslope_row_analytic {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (u : ℝ) :
    AnalyticAt ℝ (fun t => dslope f t u) 0 := by
  by_cases hu : u = 0
  · subst u
    have he : (fun t => dslope f t 0) = dslope f 0 := funext (fun t => carryScalar_dslope_symm f t 0)
    rw [he]
    exact carryScalarJetShift_analytic hf 1
  · have ha : AnalyticAt ℝ (fun t : ℝ => ((u-t : ℝ) : ℂ)) 0 := by
      convert (analyticAt_const (v := (u : ℂ))).sub (Complex.ofRealCLM.analyticAt 0) using 1
      ext t
      simp only [Complex.ofReal_sub,Complex.ofRealCLM_apply,Pi.sub_apply]
    exact (((analyticAt_const.sub hf).div ha (by simpa using hu)).congr (row_germ f u hu).symm)

/-- Interchanging a central divided difference with the first kernel slot.
The diagonal uses actual scalar derivatives, not cancellation of zero factors. -/
theorem carryScalar_dslope_left_comm (f : ℝ → ℂ) (t u : ℝ)
    (h0 : DifferentiableAt ℝ f 0) (ht : DifferentiableAt ℝ f t) :
    dslope (fun x => dslope f x u) 0 t = dslope (dslope f 0) t u := by
  by_cases hu : u = 0
  · subst u
    have he : (fun x => dslope f x 0) = dslope f 0 := funext (fun x => carryScalar_dslope_symm f x 0)
    rw [he, carryScalar_dslope_symm (dslope f 0) 0 t]
  · have huc : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    by_cases hz : t = 0
    · subst t
      have hd := ((hasDerivAt_const (0 : ℝ) (f u)).sub h0.hasDerivAt).div
        (((hasDerivAt_const (0 : ℝ) (u : ℂ)).sub (hasDerivAt_id (0 : ℝ)).ofReal_comp))
        (by simpa using huc)
      have hg := hd.congr_of_eventuallyEq (by
        filter_upwards [row_germ f u hu] with x hx
        simpa only [Complex.ofReal_sub,Pi.sub_apply,Pi.div_apply,id_eq] using hx)
      rw [dslope_same, hg.deriv, dslope_of_ne _ hu]
      simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_inv]
      rw [dslope_same,dslope_of_ne _ hu]
      simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_zero,
        Complex.ofReal_inv,zero_sub,Pi.sub_apply,id_eq,Complex.ofReal_one]
      field_simp
      ring
    · have htc : (t : ℂ) ≠ 0 := by exact_mod_cast hz
      by_cases he : u = t
      · subst u
        have hd := (ht.hasDerivAt.sub_const (f 0)).div
          (hasDerivAt_id t).ofReal_comp htc
        have hn : ∀ᶠ x : ℝ in nhds t, x ≠ 0 := isOpen_ne.mem_nhds hz
        have hg : (fun x : ℝ => (f x-f 0)/(x : ℂ)) =ᶠ[nhds t] dslope f 0 := by
          filter_upwards [hn] with x hx
          simp [dslope_of_ne _ hx,slope,Complex.real_smul,div_eq_mul_inv,mul_comm]
        have hd' := hd.congr_of_eventuallyEq hg.symm
        rw [dslope_of_ne _ hz,dslope_same,hd'.deriv]
        simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_inv]
        rw [dslope_same,dslope_of_ne _ hz]
        simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_inv,Complex.ofReal_one,id_eq]
        field_simp
      · rw [dslope_of_ne _ hz,dslope_of_ne _ he]
        simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_inv]
        simp only [dslope_of_ne _ hu,dslope_of_ne _ he,dslope_of_ne _ hz]
        simp only [slope,Complex.real_smul,vsub_eq_sub,sub_zero,Complex.ofReal_inv]
        have hdiff : ((u-t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr he
        push_cast at hdiff ⊢
        field_simp
        ring

theorem carryScalar_dslope_row_shift {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (p : ℕ) (u : ℝ) :
    carryScalarJetShift p (fun t => dslope f t u) =ᶠ[nhds 0]
      (fun t => dslope (carryScalarJetShift p f) t u) := by
  induction p with
  | zero => exact Filter.EventuallyEq.rfl
  | succ p ih =>
    have h := carryScalarJetShift_germ ih 1
    have ha := carryScalarJetShift_analytic hf p
    filter_upwards [h,ha.eventually_analyticAt] with t ht hreg
    change dslope (carryScalarJetShift p (fun x => dslope f x u)) 0 t = _ at ht
    rw [carryScalarJetShift_succ p (fun x => dslope f x u),ht,carryScalarJetShift_succ p f]
    exact carryScalar_dslope_left_comm _ _ _ ha.differentiableAt hreg.differentiableAt

private theorem shift_sub_mul (f g : ℝ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (n : ℕ) :
    carryScalarJetShift n (fun t => f t-g t*c) =
      fun t => carryScalarJetShift n f t-carryScalarJetShift n g t*c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [carryScalarJetShift_succ,ih,carryScalarJetShift_succ,carryScalarJetShift_succ]
    funext t
    by_cases ht : t = 0
    · subst t
      simp only [dslope_same]
      exact (((carryScalarJetShift_analytic hf n).differentiableAt.hasDerivAt).sub
        (((carryScalarJetShift_analytic hg n).differentiableAt.hasDerivAt).mul_const c)).deriv
    · simp only [dslope_of_ne _ ht,slope,Complex.real_smul,vsub_eq_sub]
      ring

/-- Ordered confluent readout of a kernel, with independent left/right orders. -/
def carryKernelJet (K : ℝ → ℝ → ℂ) (p q : ℕ) : ℂ :=
  carryScalarJetShift q (fun u => carryScalarJetShift p (fun t => K t u) 0) 0

theorem carryKernelJet_germ {K L : ℝ → ℝ → ℂ}
    (h : ∀ᶠ u : ℝ in nhds 0, (fun t => K t u) =ᶠ[nhds 0] fun t => L t u)
    (p q : ℕ) : carryKernelJet K p q = carryKernelJet L p q := by
  apply (carryScalarJetShift_germ ?_ q).eq_of_nhds
  filter_upwards [h] with u hu
  exact (carryScalarJetShift_germ hu p).eq_of_nhds

/-- A derived identity for the original divided-difference kernel, not a
definition of a target Gram. It retains both independent confluent orders. -/
theorem carryKernelJet_centered {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0)
    (a : ℂ) (p q : ℕ) :
    carryKernelJet (fun t u => dslope f t u-dslope f 0 t*dslope f 0 u/a) p q =
      carryScalarJetShift (p+q+1) f 0-
        carryScalarJetShift (p+1) f 0*carryScalarJetShift (q+1) f 0/a := by
  have hr (u : ℝ) :
      carryScalarJetShift p (fun t => dslope f t u-dslope f 0 t*dslope f 0 u/a) 0 =
        carryScalarJetShift (p+1) f u-carryScalarJetShift (p+1) f 0*dslope f 0 u/a := by
    simp_rw [div_eq_mul_inv,mul_assoc]
    rw [shift_sub_mul (fun t => dslope f t u) (dslope f 0) _
      (carryScalar_dslope_row_analytic hf u) (carryScalarJetShift_analytic hf 1)]
    dsimp only
    rw [(carryScalar_dslope_row_shift hf p u).eq_of_nhds]
    have he : carryScalarJetShift p (dslope f 0) = carryScalarJetShift (p+1) f := by
      exact (carryScalarJetShift_add 1 p f).trans (by congr 1; omega)
    rw [he,carryScalarJetShift_succ p f]
  unfold carryKernelJet
  simp_rw [hr]
  have he : (fun u => carryScalarJetShift (p+1) f u-
      carryScalarJetShift (p+1) f 0*dslope f 0 u/a) =
      (fun u => carryScalarJetShift (p+1) f u-
        dslope f 0 u*(carryScalarJetShift (p+1) f 0/a)) := by funext u; ring
  rw [he,shift_sub_mul (carryScalarJetShift (p+1) f) (dslope f 0) _
    (carryScalarJetShift_analytic hf (p+1)) (carryScalarJetShift_analytic hf 1)]
  have heq : carryScalarJetShift q (dslope f 0) = carryScalarJetShift (q+1) f := by
    exact (carryScalarJetShift_add 1 q f).trans (by congr 1; omega)
  rw [carryScalarJetShift_add,heq]
  have hi : p+1+q=p+q+1 := by omega
  simp only [hi]
  ring

def carryMaterialResidualJet (p q : ℕ) : ℝ :=
  (carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q).re

def carryMaterialMixedBlock (x y v w : ℝ) : ℝ :=
  carryMaterialResidualJet 2 2*x*v+carryMaterialResidualJet 2 4*x*w+
    carryMaterialResidualJet 4 2*y*v+carryMaterialResidualJet 4 4*y*w

def carryMaterialMixedPivot : ℝ :=
  carryMaterialResidualJet 4 4-
    carryMaterialResidualJet 4 2*carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2

/-- Bilinear elimination retains two independent arguments and both ordered
crossings; no symmetry or sign is assumed here. -/
theorem carryMaterialMixedBlock_sewing (hA : carryMaterialResidualJet 2 2 ≠ 0)
    (x y v w : ℝ) :
    carryMaterialMixedBlock x y v w =
      carryMaterialResidualJet 2 2*
        (x+carryMaterialResidualJet 4 2/carryMaterialResidualJet 2 2*y)*
        (v+carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2*w)+
      carryMaterialMixedPivot*y*w := by
  unfold carryMaterialMixedBlock carryMaterialMixedPivot
  field_simp
  ring

theorem carryMaterialMixedBlock_critical (hA : carryMaterialResidualJet 2 2 ≠ 0) :
    carryMaterialMixedBlock
      (-carryMaterialResidualJet 4 2/carryMaterialResidualJet 2 2) 1
      (-carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2) 1 =
      carryMaterialMixedPivot := by
  rw [carryMaterialMixedBlock_sewing hA]
  ring

/-- The literal factor in the previously proved valve residual numerator. -/
def carryValveResidualFactor (t u : ℝ) : ℂ :=
  (2 : ℂ)*((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*
    conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*((u-t : ℝ) : ℂ)

/-- Representative for ordered central observations of the existing balance.
Division occurs only on its regular locus. The zero extension outside that
locus is only an observation representative, not a two-variable kernel
extension. The comparison proves row germs at zero before any jet is used. -/
def carryValveConfluentReadout (eta t u : ℝ) : ℂ :=
  if carryValveResidualFactor t u = 0 then 0
  else carryValveReducedReturnBalance eta t u/carryValveResidualFactor t u

theorem carryValveConfluentReadout_zero_left (eta u : ℝ) :
    carryValveConfluentReadout eta 0 u = 0 := by
  simp [carryValveConfluentReadout,carryValveResidualFactor]

theorem carryValveConfluentReadout_zero_right (eta t : ℝ) :
    carryValveConfluentReadout eta t 0 = 0 := by
  simp [carryValveConfluentReadout,carryValveResidualFactor]

theorem carryValveResidualFactor_ne_zero (t u : ℝ)
    (ha : carryMaterialResponseScale ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (htu : u ≠ t)
    (hFt : baseTwoCanonicalResponse t ≠ 0) (hFu : baseTwoCanonicalResponse u ≠ 0) :
    carryValveResidualFactor t u ≠ 0 := by
  unfold carryValveResidualFactor
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) ht) hu))
      (by simpa only [map_ne_zero] using hFt)) hFu)
        (by exact_mod_cast sub_ne_zero.mpr htu)

/-- This identity is asserted only on the regular locus. -/
theorem carryValveConfluentReadout_physical (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ)
    (hreg : carryValveResidualFactor t u ≠ 0) :
    carryValveConfluentReadout eta t u =
      (carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)-
        carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
          (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)))/
            carryValveResidualFactor t u := by
  rw [carryValveConfluentReadout,if_neg hreg,
    carryValveReducedReturnBalance_physical eta heta]

def carryValveConfluentJet (eta : ℝ) (p q : ℕ) : ℂ :=
  carryKernelJet (carryValveConfluentReadout eta) p q

def carryValveMixedBlock (eta x y v w : ℝ) : ℝ :=
  (carryValveConfluentJet eta 2 2).re*x*v+(carryValveConfluentJet eta 2 4).re*x*w+
    (carryValveConfluentJet eta 4 2).re*y*v+(carryValveConfluentJet eta 4 4).re*y*w

end
end GeometryOfNumbers.Analysis
