import CayleyFlow
import KernelTaylor
import Mathlib.Analysis.Calculus.Deriv.CompMul

namespace CarryRadialFlow
open CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def radialQuotient (h : ℂ) (i : Fin 4) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient (Complex.I*address i*h)

/-- Analytic two-argument extension of the original quotient defect in the
fixed Cauchy coordinates. Identification with physical states is separate. -/
def radialDefectEntry (h : ℂ) (i j : Fin 4) : ℂ :=
  (1-radialQuotient h i*radialQuotient h j)/(address i+address j)

theorem address_sum_ne_zero (i j : Fin 4) : address i+address j≠0 := by
  fin_cases i <;> fin_cases j <;> norm_num [address]

/-- Exact derivative identity on two independent addresses. This retains
both differentiated return factors and the full Cauchy denominator. -/
theorem radial_defect_flow (i j : Fin 4) :
    ∀ᶠ h : ℂ in nhds 0,
      h*deriv (fun z => radialDefectEntry z i j) h=
        2*radialQuotient h i*radialQuotient h j*
          (-Complex.I*(flowResponse (Complex.I*address i*h)+
            flowResponse (Complex.I*address j*h))/(address i+address j)) := by
  have ht (r : Fin 4) : Tendsto (fun h : ℂ => Complex.I*address r*h) (nhds 0) (nhds 0) := by
    simpa using (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (Complex.I*address r)
  filter_upwards [(ht i).eventually original_quotient_analytic.eventually_analyticAt,
    (ht j).eventually original_quotient_analytic.eventually_analyticAt,
    (ht i).eventually original_quotient_flow_equation,
    (ht j).eventually original_quotient_flow_equation] with h hai haj hi hj
  have hdi : HasDerivAt (fun z => radialQuotient z i)
      ((Complex.I*address i)*deriv completedNativeHermiteBiehlerChiralQuotient
        (Complex.I*address i*h)) h := by
    simpa only [radialQuotient,Function.comp_def,mul_one,mul_comm] using hai.differentiableAt.hasDerivAt.comp h
      ((hasDerivAt_id h).const_mul (Complex.I*address i))
  have hdj : HasDerivAt (fun z => radialQuotient z j)
      ((Complex.I*address j)*deriv completedNativeHermiteBiehlerChiralQuotient
        (Complex.I*address j*h)) h := by
    simpa only [radialQuotient,Function.comp_def,mul_one,mul_comm] using haj.differentiableAt.hasDerivAt.comp h
      ((hasDerivAt_id h).const_mul (Complex.I*address j))
  have he := ((hasDerivAt_const h (1:ℂ)).sub (hdi.mul hdj)).div_const (address i+address j)
  change HasDerivAt (fun z => radialDefectEntry z i j) _ h at he
  rw [he.deriv]
  have hn := address_sum_ne_zero i j
  field_simp [hn]
  unfold radialQuotient
  linear_combination (norm := ring_nf) -(completedNativeHermiteBiehlerChiralQuotient (Complex.I*address j*h))*hi-
    (completedNativeHermiteBiehlerChiralQuotient (Complex.I*address i*h))*hj

end
end CarryRadialFlow
