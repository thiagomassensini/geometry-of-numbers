import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-! A complex Hilbert carrier built from the real Hilbert space by two real
quadratures. This is used to form the complex resolvent of the real moment
multiplier. -/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarryMomentLogConvex

noncomputable section

/-- The canonical Hilbert complexification of a real Hilbert space. -/
def RealHilbertComplexification (E : Type*) := WithLp 2 (E × E)

namespace RealHilbertComplexification

variable {E : Type*}

instance [NormedAddCommGroup E] : NormedAddCommGroup
    (RealHilbertComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [NormedAddCommGroup E] [CompleteSpace E] : CompleteSpace
    (RealHilbertComplexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

/-- Real coordinate of a complexified vector. -/
def re [NormedAddCommGroup E] (x : RealHilbertComplexification E) : E :=
  (WithLp.ofLp x).1

/-- Imaginary coordinate of a complexified vector. -/
def im [NormedAddCommGroup E] (x : RealHilbertComplexification E) : E :=
  (WithLp.ofLp x).2

/-- Package two real vectors as one vector in the complexification. -/
def mk [NormedAddCommGroup E] (x y : E) : RealHilbertComplexification E :=
  WithLp.toLp 2 (x, y)

@[simp] theorem re_mk [NormedAddCommGroup E] (x y : E) :
    re (mk x y) = x := rfl

@[simp] theorem im_mk [NormedAddCommGroup E] (x y : E) :
    im (mk x y) = y := rfl

@[simp] theorem re_zero [NormedAddCommGroup E] :
    re (0 : RealHilbertComplexification E) = 0 := rfl

@[simp] theorem im_zero [NormedAddCommGroup E] :
    im (0 : RealHilbertComplexification E) = 0 := rfl

@[simp] theorem re_add [NormedAddCommGroup E]
    (x y : RealHilbertComplexification E) :
    re (x + y) = re x + re y := rfl

@[simp] theorem im_add [NormedAddCommGroup E]
    (x y : RealHilbertComplexification E) :
    im (x + y) = im x + im y := rfl

@[simp] theorem re_neg [NormedAddCommGroup E]
    (x : RealHilbertComplexification E) :
    re (-x) = -re x := rfl

@[simp] theorem im_neg [NormedAddCommGroup E]
    (x : RealHilbertComplexification E) :
    im (-x) = -im x := rfl

@[ext] theorem ext [NormedAddCommGroup E]
    {x y : RealHilbertComplexification E}
    (hre : re x = re y) (him : im x = im y) : x = y := by
  apply WithLp.ofLp_injective 2
  exact Prod.ext hre him

/-- Canonical complex scalar multiplication on two real quadratures. -/
def complexSMul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    RealHilbertComplexification E :=
  mk (z.re • re x - z.im • im x)
    (z.im • re x + z.re • im x)

@[reducible] instance [NormedAddCommGroup E] [Module ℝ E] :
    SMul ℂ (RealHilbertComplexification E) :=
  ⟨complexSMul⟩

@[simp] theorem re_smul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    re (z • x) = z.re • re x - z.im • im x := rfl

@[simp] theorem im_smul [NormedAddCommGroup E] [Module ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    im (z • x) = z.im • re x + z.re • im x := rfl

@[reducible] private def complexModule
    [NormedAddCommGroup E] [Module ℝ E] :
    Module ℂ (RealHilbertComplexification E) where
  smul := complexSMul
  one_smul x := by ext <;> simp
  mul_smul z w x := by
    ext <;> simp [Complex.mul_re, Complex.mul_im] <;> module
  smul_zero z := by ext <;> simp
  smul_add z x y := by ext <;> simp <;> module
  add_smul z w x := by ext <;> simp <;> module
  zero_smul x := by ext <;> simp

/-- The canonical complex inner product on the complexification. -/
def complexInner [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) : ℂ :=
  ((inner ℝ (re x) (re y) + inner ℝ (im x) (im y) : ℝ) : ℂ) +
    Complex.I *
      ((inner ℝ (re x) (im y) - inner ℝ (im x) (re y) : ℝ) : ℂ)

private theorem norm_complexSMul_sq
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : ℂ) (x : RealHilbertComplexification E) :
    ‖z • x‖ ^ 2 = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 x
  calc
    ‖z • x‖ ^ 2 =
        ‖z.re • re x - z.im • im x‖ ^ 2 +
          ‖z.im • re x + z.re • im x‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 (z • x)
    _ = ‖z‖ ^ 2 * (‖re x‖ ^ 2 + ‖im x‖ ^ 2) := by
      rw [norm_sub_sq_real, norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs,
        real_inner_smul_left, real_inner_smul_right]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [mul_pow, sq_abs]
      ring
    _ = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by rw [hx]

@[reducible] private def complexNormedSpace
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    NormedSpace ℂ (RealHilbertComplexification E) where
  __ := complexModule
  norm_smul_le z x := by
    have hsq := norm_complexSMul_sq z x
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa [mul_pow] using le_of_eq hsq

instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    InnerProductSpace ℂ (RealHilbertComplexification E) where
  __ := complexNormedSpace
  inner := complexInner
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = (complexInner x x).re
    calc
      ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 x
      _ = (complexInner x x).re := by
        simp only [complexInner, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, sub_self, add_zero]
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  conj_inner_symm x y := by
    apply Complex.ext <;>
      simp [complexInner, real_inner_comm]
  add_left x y z := by
    apply Complex.ext <;>
      simp [complexInner, inner_add_left] <;> ring
  smul_left x y z := by
    apply Complex.ext <;>
      simp [complexInner, Complex.mul_re, Complex.mul_im,
        inner_sub_left, inner_add_left, real_inner_smul_left] <;>
      ring

@[simp] theorem inner_apply
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    inner ℂ x y = complexInner x y := rfl

@[simp] theorem complexInner_re
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    (complexInner x y).re =
      inner ℝ (re x) (re y) + inner ℝ (im x) (im y) := by
  simp [complexInner]

@[simp] theorem complexInner_im
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : RealHilbertComplexification E) :
    (complexInner x y).im =
      inner ℝ (re x) (im y) - inner ℝ (im x) (re y) := by
  simp [complexInner]

end RealHilbertComplexification

end

#print axioms CarryMomentLogConvex.RealHilbertComplexification.inner_apply
