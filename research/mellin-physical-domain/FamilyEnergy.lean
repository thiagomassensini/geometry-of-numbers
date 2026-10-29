import BoundaryFamily
import PolynomialIntegrals

namespace CarryMellinDomain
open CarrySelfAdjointOperator MeasureTheory
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

/-- Full synthesized energy: all finite binomial crosses are still present. -/
theorem physical_concentration_energy_integral (n : ℕ) :
    ‖physicalConcentration n‖^2=((n:ℝ)+1)^2*
      (∫ u in (0:ℝ)..1, u^3*(1-u)^(2*n)) := by
  have hi : inner ℂ (physicalConcentration n) (physicalConcentration n)=
      ((((n:ℝ)+1)^2*(∫ u in (0:ℝ)..1, u^3*(1-u)^(2*n)):ℝ):ℂ) := by
    rw [physicalConcentration,ContinuousMap.inner_toLp]
    change (∫ u : unitInterval,
      concentratingContinuous n u*conj (concentratingContinuous n u))=_
    have he : (fun u : unitInterval =>
        concentratingContinuous n u*conj (concentratingContinuous n u))=
        fun u : unitInterval => ((((n:ℝ)+1)^2*((u:ℝ)^3*(1-(u:ℝ))^(2*n)):ℝ):ℂ) := by
      funext u
      rw [concentrating_source_original,Complex.conj_ofReal,← Complex.ofReal_mul]
      congr 1
      calc
        _ = ((n:ℝ)+1)^2*(Real.sqrt (u:ℝ))^2*(u:ℝ)^2*((1-(u:ℝ))^n)^2 := by ring
        _ = ((n:ℝ)+1)^2*((u:ℝ)^3*(1-(u:ℝ))^(2*n)) := by
          rw [Real.sq_sqrt u.property.1,show 2*n=n*2 by omega,pow_mul]
          ring

    rw [he]
    have hs : (∫ u : unitInterval, ((((n:ℝ)+1)^2*((u:ℝ)^3*(1-(u:ℝ))^(2*n)):ℝ):ℂ))=
        ∫ u in Set.Icc (0:ℝ) 1, ((((n:ℝ)+1)^2*(u^3*(1-u)^(2*n)):ℝ):ℂ) := by
      simpa only [unitInterval.volume_def] using
        (integral_subtype_comap (μ:=(volume:Measure ℝ))
          (measurableSet_Icc : MeasurableSet (Set.Icc (0:ℝ) 1))
          (fun u : ℝ => ((((n:ℝ)+1)^2*(u^3*(1-u)^(2*n)):ℝ):ℂ)))
    rw [hs]
    have ht : (∫ u in Set.Icc (0:ℝ) 1, ((((n:ℝ)+1)^2*(u^3*(1-u)^(2*n)):ℝ):ℂ))=
        ∫ u in (0:ℝ)..1, ((((n:ℝ)+1)^2*(u^3*(1-u)^(2*n)):ℝ):ℂ) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
        setIntegral_congr_set Ioc_ae_eq_Icc]
    rw [ht,intervalIntegral.integral_ofReal,intervalIntegral.integral_const_mul]
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),hi]
  rfl

/-- Exact rational energy of the unchanged physical finite source. -/
theorem physical_concentration_norm_sq (n : ℕ) :
    ‖physicalConcentration n‖^2=
      6*((n:ℝ)+1)^2/((2*(n:ℝ)+1)*(2*(n:ℝ)+2)*(2*(n:ℝ)+3)*(2*(n:ℝ)+4)) := by
  rw [physical_concentration_energy_integral,cubic_one_sub_integral]
  push_cast
  ring

/-- A dimension-independent elementary bound; no source precision involved. -/
theorem physical_concentration_norm_sq_le (n : ℕ) :
    ‖physicalConcentration n‖^2≤6/((n:ℝ)+1)^2 := by
  rw [physical_concentration_norm_sq]
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have h1 : 0<(n:ℝ)+1 := by positivity
  have hd : 0<(2*(n:ℝ)+1)*(2*(n:ℝ)+2)*(2*(n:ℝ)+3)*(2*(n:ℝ)+4) := by positivity
  apply (div_le_div_iff₀ hd (sq_pos_of_pos h1)).mpr
  nlinarith [sq_nonneg ((n:ℝ)^2),sq_nonneg (n:ℝ)]

end
end CarryMellinDomain
