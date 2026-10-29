import KernelBudget

/-! The off-diagonal correction required by the ORIGINAL spectral separation.
A product of diagonal energy scales is not the two-argument Green factor. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp
open scoped InnerProductSpace ComplexConjugate
noncomputable section

/-- Exact difference between native spectral separation and the product of
the two diagonal scales. This does not define a replacement metric. -/
def separationCorrection (z w : ℂ) : ℂ :=
  (w-conj z)-Complex.I*
    Complex.ofReal (Real.sqrt (2*z.im)*Real.sqrt (2*w.im))

theorem defectPair_signature (z w : ℂ) (u v : Source) :
    defectPair z w u v=signaturePair z w u v-
      Complex.ofReal (Real.sqrt (2*z.im)*Real.sqrt (2*w.im))*
        inner ℂ (ambientReadout u) (ambientReadout v) := by
  have he : inner ℂ (enlargedReadout z u) (enlargedReadout w v)=
      Complex.ofReal (Real.sqrt (2*z.im)*Real.sqrt (2*w.im))*
        inner ℂ (ambientReadout u) (ambientReadout v)+
          inner ℂ (minusReadout z u) (minusReadout w v) := by
    change inner ℂ
      (WithLp.toLp 2 ((Real.sqrt (2*z.im) : ℂ) • ambientReadout u,minusReadout z u))
      (WithLp.toLp 2 ((Real.sqrt (2*w.im) : ℂ) • ambientReadout v,minusReadout w v))=_
    rw [WithLp.prod_inner_apply]
    change inner ℂ ((Real.sqrt (2*z.im) : ℂ) • ambientReadout u)
      ((Real.sqrt (2*w.im) : ℂ) • ambientReadout v)+_=_
    rw [inner_smul_left,inner_smul_right]
    simp only [Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  unfold defectPair signaturePair
  rw [he]
  push_cast
  ring

/-- The complete native residual, including the off-diagonal scale defect. -/
theorem native_four_channel_separation_correction (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1 =
      -Complex.I*defectPair z w (nativeSource z hs) (nativeSource w ht)+
        separationCorrection z w*inner ℂ
          (ambientReadout (fiberPart (nativeSource z hs)))
          (ambientReadout (fiberPart (nativeSource w ht))) := by
  rw [native_four_channel_fiber_identity z w hz hw hs ht,defectPair_signature,
    ambient_fiber,ambient_fiber,signature_trace]
  unfold separationCorrection
  ring

/-- The missing factor is invisible to every upper-half-plane diagonal. -/
theorem separationCorrection_diagonal (z : ℂ) (hz : 0 ≤ z.im) :
    separationCorrection z z=0 := by
  have hsep : z-conj z=Complex.I*Complex.ofReal (2*z.im) := by
    (apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]); ring
  have hsq : Real.sqrt (2*z.im)*Real.sqrt (2*z.im)=2*z.im := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2*z.im)]
  unfold separationCorrection
  rw [hsep,hsq,sub_self]

private theorem sqrt_two_product (a b : ℝ) :
    Real.sqrt (2*a)*Real.sqrt (2*b)=2*Real.sqrt a*Real.sqrt b := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = (Real.sqrt 2)^2*Real.sqrt a*Real.sqrt b := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- On original radial points the correction is a squared distance of the
square-root radii, with its exact imaginary orientation. -/
theorem separationCorrection_radial (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    separationCorrection (Complex.I*(a : ℂ)) (Complex.I*(b : ℂ))=
      Complex.I*Complex.ofReal ((Real.sqrt a-Real.sqrt b)^2) := by
  have hn : a+b-Real.sqrt (2*a)*Real.sqrt (2*b)=(Real.sqrt a-Real.sqrt b)^2 := by
    rw [sqrt_two_product]
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]
  have hc := congrArg Complex.ofReal hn
  push_cast at hc
  unfold separationCorrection
  rw [show (Complex.I*(a : ℂ)).im=a by simp,
      show (Complex.I*(b : ℂ)).im=b by simp]
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_sub]
  linear_combination Complex.I*hc

theorem separationCorrection_radial_ne_zero (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    separationCorrection (Complex.I*(a : ℂ)) (Complex.I*(b : ℂ)) ≠ 0 := by
  rw [separationCorrection_radial a b ha hb]
  intro h
  have hc : Complex.ofReal ((Real.sqrt a-Real.sqrt b)^2)=0 :=
    (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  have hr : (Real.sqrt a-Real.sqrt b)^2=0 := by exact_mod_cast hc
  have heq : Real.sqrt a=Real.sqrt b := by nlinarith
  have hsa := Real.sq_sqrt ha
  rw [heq] at hsa
  exact hab (hsa.symm.trans (Real.sq_sqrt hb))

/-- Two distinct admissible native points already detect the correction.
Both operator parameters lie strictly inside the original critical strip. -/
theorem admissible_separation_correction_nonzero :
    operatorHeightParameter (Complex.I*Complex.ofReal (1/16 : ℝ)) ∈ genuineCriticalStrip ∧
    operatorHeightParameter (Complex.I*Complex.ofReal (1/64 : ℝ)) ∈ genuineCriticalStrip ∧
    separationCorrection (Complex.I*Complex.ofReal (1/16 : ℝ)) (Complex.I*Complex.ofReal (1/64 : ℝ)) ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · constructor <;> norm_num [operatorHeightParameter]
  · constructor <;> norm_num [operatorHeightParameter]
  · exact separationCorrection_radial_ne_zero (1/16) (1/64) (by norm_num) (by norm_num) (by norm_num)

end
end CarryFiberTransport
