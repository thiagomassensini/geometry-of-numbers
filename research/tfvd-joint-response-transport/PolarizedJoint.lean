import JointExtraction

namespace CarryTfvdJoint
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Polarized joint numerator. The PLUS sign between the log jets comes from
conjugating i; it must not be replaced by the antisymmetric ordinary determinant. -/
def polarizedNumerator (Ta La Ba Tz Lz Bz : ℂ) : ℂ :=
  conj Ta * Tz * (Bz-conj Ba) + Complex.I*(conj Ta*Lz+conj La*Tz)

theorem polarizedNumerator_quotient (Ta La Ba Tz Lz Bz : ℂ)
    (ha : Ta ≠ 0) (hz : Tz ≠ 0) :
    polarizedNumerator Ta La Ba Tz Lz Bz =
      conj Ta*Tz*((Bz+Complex.I*Lz/Tz)-conj (Ba+Complex.I*La/Ta)) := by
  have hca : conj Ta ≠ 0 := by simpa using ha
  unfold polarizedNumerator
  simp only [map_add,map_div₀,map_mul,Complex.conj_I]
  field_simp
  ring

/-- Original whole two-port source of a single material coordinate.
The ambient pair is synthesized BEFORE the signed pairing is taken. -/
def basisSource (N k : ℕ) (theta : Fin N → ℂ) (i : Fin N) :=
  twoPortSynthesis N k (Pi.single i 1) (Pi.single i (theta i))

theorem basisSource_pairing (N k : ℕ) (theta eta : Fin N → ℂ) (i j : Fin N) :
    canonicalCompletedNativeProjectiveChiralForm
      (basisSource N k theta i) (basisSource N k eta j) =
      (Complex.I*((k : ℂ)+1)/2) * (cauchyMatrix N i j) * (conj (theta i)-eta j) := by
  rw [basisSource,basisSource,twoPort_signed_form]
  simp [matrixPairing,Matrix.mulVec,dotProduct,Pi.single_apply,apply_ite]
  ring

/-- Shifted radial denominator paired with the literal Cauchy entry. -/
theorem radial_cauchy_denominator (N k : ℕ) (i j : Fin N) :
    (canonicalCompletedC3RadialTiltPoint k j - conj (canonicalCompletedC3RadialTiltPoint k i)) *
      (Complex.I*((k : ℂ)+1)/2) * (cauchyMatrix N i j) = -1/2 := by
  have hK : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hD : (i.val : ℂ)+(j.val : ℂ)+2 ≠ 0 := by
    exact_mod_cast (show (i.val : ℝ)+(j.val : ℝ)+2 ≠ 0 by positivity)
  simp only [canonicalCompletedC3RadialTiltPoint,canonicalCompletedC3RadialTiltStep,
    canonicalGreenJetStep,cauchyMatrix,cauchyEntry,map_mul,map_inv₀,map_add,map_natCast,
    map_one,Complex.conj_I,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,Nat.cast_add,Nat.cast_one]
  field_simp
  simp only [Complex.I_sq]
  ring

/-- Exact two-input multiplied kernel. No positivity assumption, new metric,
or deletion of the off-diagonal sectors is used. -/
theorem physical_polarized_numerator (N M P k : ℕ) (i j : Fin N)
    (hi : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hj : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip)
    (hFi : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hFj : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    2 * (canonicalCompletedC3RadialTiltPoint k j - conj (canonicalCompletedC3RadialTiltPoint k i)) *
      (conj (value M (canonicalCompletedC3RadialTiltPoint k i))*
        value P (canonicalCompletedC3RadialTiltPoint k j)) *
      canonicalCompletedNativeProjectiveChiralForm
        (basisSource N k (fun a => originalResponse (canonicalCompletedC3RadialTiltPoint k a)) i)
        (basisSource N k (fun a => originalResponse (canonicalCompletedC3RadialTiltPoint k a)) j) =
      polarizedNumerator
        (value M (canonicalCompletedC3RadialTiltPoint k i))
        (logJet M (canonicalCompletedC3RadialTiltPoint k i))
        (completionResponse (canonicalCompletedC3RadialTiltPoint k i))
        (value P (canonicalCompletedC3RadialTiltPoint k j))
        (logJet P (canonicalCompletedC3RadialTiltPoint k j))
        (completionResponse (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [polarizedNumerator_quotient
    (value M (canonicalCompletedC3RadialTiltPoint k i))
    (logJet M (canonicalCompletedC3RadialTiltPoint k i))
    (completionResponse (canonicalCompletedC3RadialTiltPoint k i))
    (value P (canonicalCompletedC3RadialTiltPoint k j))
    (logJet P (canonicalCompletedC3RadialTiltPoint k j))
    (completionResponse (canonicalCompletedC3RadialTiltPoint k j))
    (tfvdCanonicalResponse_regular_denominators M _ hi hFi).2.2
    (tfvdCanonicalResponse_regular_denominators P _ hj hFj).2.2,
    full_response M _ hi hFi,full_response P _ hj hFj,basisSource_pairing]
  have hd := radial_cauchy_denominator N k i j
  linear_combination
    -2 * (conj (value M (canonicalCompletedC3RadialTiltPoint k i))*
      value P (canonicalCompletedC3RadialTiltPoint k j)) *
      (originalResponse (canonicalCompletedC3RadialTiltPoint k j)-
        conj (originalResponse (canonicalCompletedC3RadialTiltPoint k i))) * hd


/-- The entire two-input graph pairing, with EVERY ordered crossing retained. -/
theorem graph_pairing_sum (N k : ℕ) (theta eta v w : Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v (fun i => theta i*v i))
      (twoPortSynthesis N k w (fun j => eta j*w j)) =
      ∑ i, ∑ j, conj (v i)*w j *
        canonicalCompletedNativeProjectiveChiralForm
          (basisSource N k theta i) (basisSource N k eta j) := by
  simp_rw [basisSource_pairing]
  rw [twoPort_signed_form]
  unfold matrixPairing Matrix.mulVec dotProduct
  simp only [Pi.star_apply,RCLike.star_def,map_mul,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The recombined physical numerator is the graph kernel at two independent
radial nodes. Only the full T values are divided, after both channels are assembled. -/
theorem physical_basis_quotient (N M P k : ℕ) (i j : Fin N)
    (hi : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hj : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip)
    (hFi : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hFj : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (basisSource N k (fun a => originalResponse (canonicalCompletedC3RadialTiltPoint k a)) i)
      (basisSource N k (fun a => originalResponse (canonicalCompletedC3RadialTiltPoint k a)) j) =
      polarizedNumerator
        (value M (canonicalCompletedC3RadialTiltPoint k i))
        (logJet M (canonicalCompletedC3RadialTiltPoint k i))
        (completionResponse (canonicalCompletedC3RadialTiltPoint k i))
        (value P (canonicalCompletedC3RadialTiltPoint k j))
        (logJet P (canonicalCompletedC3RadialTiltPoint k j))
        (completionResponse (canonicalCompletedC3RadialTiltPoint k j)) /
      (2*(canonicalCompletedC3RadialTiltPoint k j-conj (canonicalCompletedC3RadialTiltPoint k i))*
        (conj (value M (canonicalCompletedC3RadialTiltPoint k i))*
          value P (canonicalCompletedC3RadialTiltPoint k j))) := by
  have hd := radial_cauchy_denominator N k i j
  have hrad : canonicalCompletedC3RadialTiltPoint k j -
      conj (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hd
    norm_num at hd
  have hTi := (tfvdCanonicalResponse_regular_denominators M _ hi hFi).2.2
  have hTj := (tfvdCanonicalResponse_regular_denominators P _ hj hFj).2.2
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hrad)
    (mul_ne_zero (by simpa [value] using hTi) hTj))).mpr
  rw [mul_comm]
  exact physical_polarized_numerator N M P k i j hi hj hFi hFj


/-- Actual polarized center readout, with independently chosen exact cutoffs.
The division is of the FULL value pair, after the crossed numerator is assembled. -/
def centeredPolarizedReadout (M P : ℕ) (z : ℂ) : ℂ :=
  polarizedNumerator (value M 0) (logJet M 0) (completionResponse 0)
    (value P z) (logJet P z) (completionResponse z) /
      (conj (value M 0)*value P z)

/-- On the physical germ this is precisely the completed response, with its
central value cancelled by evenness, rather than by fitting a constant. -/
theorem centeredPolarizedReadout_eventuallyEq (M P : ℕ) :
    centeredPolarizedReadout M P =ᶠ[nhds (0 : ℂ)] originalResponse := by
  have hF := completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
    completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds
    zero_mem_completedNativeHeightDomain,hF] with z hz hFz
  have hTz : value P z ≠ 0 := (tfvdCanonicalResponse_regular_denominators P z hz hFz).2.2
  unfold centeredPolarizedReadout
  rw [polarizedNumerator_quotient (value M 0) (logJet M 0) (completionResponse 0)
    (value P z) (logJet P z) (completionResponse z) (value_zero_ne M) hTz,
    full_response M 0 zero_mem_completedNativeHeightDomain
      completedNativeOperatorCharacteristic_zero_ne_zero,
    full_response P z hz hFz,full_response_zero,map_zero,sub_zero]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by simpa using value_zero_ne M) hTz)

/-- Every canonical coefficient is recovered from the physical polarized germ.
This coefficient identity is not a positive Gram identity. -/
theorem centeredPolarizedReadout_odd_coefficient (M P n : ℕ) :
    iteratedDeriv (2*n+1) (centeredPolarizedReadout M P) 0 / ((2*n+1).factorial : ℂ) =
      2*(canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  have he := (centeredPolarizedReadout_eventuallyEq M P).trans
    (normalizedCenteredNumerator_eventuallyEq M).symm
  rw [he.iteratedDeriv_eq (2*n+1)]
  exact normalizedCenteredNumerator_odd_coefficient M n

end
end CarryTfvdJoint
