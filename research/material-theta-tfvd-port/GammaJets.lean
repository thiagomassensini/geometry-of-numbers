import FluxComparison
import NativeCarrySpectralWeyl.Camera.DerivativeTail
import NativeCarrySpectralWeyl.Camera.ModalEnergy

/-! The Mellin-calibrated finite source INCLUDING its actual Gamma derivative.
Its negative derivative companion is not theta-coordinate differentiation.
The two-parameter Green correction is retained without a sign assumption. -/
namespace CarryMaterialTheta
open CarrySelfAdjointOperator NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Boundary Filter
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def finiteMaterialValue (N : ℕ) (a : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ i : Fin N, a i * dirichletValue s (i.val+1)

def finiteMaterialLog (N : ℕ) (a : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ i : Fin N, a i * (Real.log ((i.val+1 : ℕ) : ℝ) : ℂ) *
    dirichletValue s (i.val+1)

theorem finiteMaterialValue_hasDerivAt (N : ℕ) (a : Fin N → ℂ) (s : ℂ) :
    HasDerivAt (finiteMaterialValue N a) (-finiteMaterialLog N a s) s := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
    (fun i _ => (dirichletValue_hasDerivAt (by omega : 0 < i.val+1) s).const_mul (a i))
  have hfun : finiteMaterialValue N a =
      ∑ i : Fin N, (fun z => a i * dirichletValue z (i.val+1)) := by
    funext z
    simp [finiteMaterialValue]
  have hd : -finiteMaterialLog N a s =
      ∑ i : Fin N, a i * dirichletValueExponentDeriv s (i.val+1) := by
    simp [finiteMaterialLog, dirichletValueExponentDeriv, mul_assoc]
  rw [← hfun, ← hd] at h
  exact h

theorem heat_mellin_material_value (N : ℕ) (a : Fin N → ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (finiteHeatSynthesis N a) (s/2) = Complex.Gammaℝ s * finiteMaterialValue N a s := by
  rw [finite_heat_mellin N a hs]
  simp only [finiteMaterialValue, dirichletValue, Complex.cpow_neg, div_eq_mul_inv]

theorem heat_mellin_material_log (N : ℕ) (a : Fin N → ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (finiteHeatSynthesis N
      (fun i => a i * (Real.log ((i.val+1 : ℕ) : ℝ) : ℂ))) (s/2) =
        Complex.Gammaℝ s * finiteMaterialLog N a s := by
  rw [finite_heat_mellin N _ hs]
  simp only [finiteMaterialLog, dirichletValue, Complex.cpow_neg, div_eq_mul_inv]

/-- Identification with the ORIGINAL native Xi dressing, including its
polynomial factor. GammaR is not a replacement completion. -/
theorem native_completion_eq_gammaR (z : ℂ) :
    nativeXiCompletionFactor z =
      (1/2 : ℂ)*operatorHeightParameter z*(operatorHeightParameter z-1)*
        Complex.Gammaℝ (operatorHeightParameter z) := by
  rw [nativeXiCompletionFactor, Complex.Gammaℝ_def,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  rw [← Complex.ofReal_log Real.pi_pos.le]
  have he : (Real.log Real.pi : ℂ) * (-operatorHeightParameter z/2) =
      -(operatorHeightParameter z/2) * (Real.log Real.pi : ℂ) := by ring
  rw [he]
  ring

theorem original_completed_finite_value_mellin (N : ℕ) (a : Fin N → ℂ)
    (z : ℂ) (hz : 0 < (operatorHeightParameter z).re) :
    nativeXiCompletionFactor z * finiteMaterialValue N a (operatorHeightParameter z) =
      ((1/2 : ℂ)*operatorHeightParameter z*(operatorHeightParameter z-1)) *
        mellin (finiteHeatSynthesis N a) (operatorHeightParameter z/2) := by
  rw [native_completion_eq_gammaR, heat_mellin_material_value N a hz]
  ring

theorem gammaR_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have h :=
    (Complex.differentiable_Gammaℝ_inv s).inv
      (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs))
  have he : (fun z : ℂ => (Complex.Gammaℝ z)⁻¹)⁻¹ = Complex.Gammaℝ := by
    funext z
    simp
  rw [he] at h
  exact h

/-- Parameter differentiation includes the original Gamma correction. -/
theorem finite_heat_mellin_hasDerivAt (N : ℕ) (a : Fin N → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => mellin (finiteHeatSynthesis N a) (z/2))
      (deriv Complex.Gammaℝ s * finiteMaterialValue N a s -
        Complex.Gammaℝ s * finiteMaterialLog N a s) s := by
  have h := (gammaR_differentiableAt hs).hasDerivAt.mul
    (finiteMaterialValue_hasDerivAt N a s)
  have heq : (fun z : ℂ => mellin (finiteHeatSynthesis N a) (z/2)) =ᶠ[nhds s]
      (fun z => Complex.Gammaℝ z * finiteMaterialValue N a z) := by
    have hdom : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hdom] with z hz
    exact heat_mellin_material_value N a hz
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  ring

def gammaDress (s : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.Gammaℝ s*p.1,
    Complex.Gammaℝ s*p.2 - deriv Complex.Gammaℝ s*p.1)

/-- Actual value/negative-derivative pair of the finite Mellin response. -/
theorem gammaDress_eq_mellin_trace (N : ℕ) (a : Fin N → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    gammaDress s (finiteMaterialValue N a s,finiteMaterialLog N a s) =
      (mellin (finiteHeatSynthesis N a) (s/2),
        -deriv (fun z : ℂ => mellin (finiteHeatSynthesis N a) (z/2)) s) := by
  rw [heat_mellin_material_value N a hs, (finite_heat_mellin_hasDerivAt N a hs).deriv]
  simp only [gammaDress]
  congr 1
  ring

/-- The native height parameter contributes its original factor I. This
chain factor is retained, rather than identifying s and height derivatives. -/
theorem native_height_mellin_hasDerivAt (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : 0 < (nativeLineComplex z).re) :
    HasDerivAt (fun w : ℂ => mellin (finiteHeatSynthesis N a) (nativeLineComplex w/2))
      (Complex.I * (deriv Complex.Gammaℝ (nativeLineComplex z) *
        finiteMaterialValue N a (nativeLineComplex z) -
        Complex.Gammaℝ (nativeLineComplex z) * finiteMaterialLog N a (nativeLineComplex z))) z := by
  have hline := hasDerivAt_nativeLineComplex z
  apply ((finite_heat_mellin_hasDerivAt N a hz).comp z hline).congr_deriv
  ring

theorem native_height_gamma_trace (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : 0 < (nativeLineComplex z).re) :
    let p := gammaDress (nativeLineComplex z)
      (finiteMaterialValue N a (nativeLineComplex z), finiteMaterialLog N a (nativeLineComplex z))
    (p.1,Complex.I*p.2) =
      (mellin (finiteHeatSynthesis N a) (nativeLineComplex z/2),
        -deriv (fun w : ℂ => mellin (finiteHeatSynthesis N a) (nativeLineComplex w/2)) z) := by
  dsimp only
  rw [heat_mellin_material_value N a hz, (native_height_mellin_hasDerivAt N a z hz).deriv]
  simp only [gammaDress]
  congr 1
  ring

/-- Full polarized Gamma Green identity, with independent parameters and
inputs. Its extra value-value channel must not be discarded. -/
theorem gammaDress_green_defect (s t : ℂ) (p q : ℂ × ℂ) :
    greenForm (𝕜 := ℂ) (gammaDress s p) (gammaDress t q) =
      ((starRingEnd ℂ) (Complex.Gammaℝ s))*Complex.Gammaℝ t *
        greenForm (𝕜 := ℂ) p q +
      (((starRingEnd ℂ) (Complex.Gammaℝ s))*deriv Complex.Gammaℝ t -
        ((starRingEnd ℂ) (deriv Complex.Gammaℝ s))*Complex.Gammaℝ t) *
          inner ℂ p.1 q.1 := by
  simp only [greenForm, gammaDress, RCLike.inner_apply', map_mul, map_sub]
  ring

end
end CarryMaterialTheta
