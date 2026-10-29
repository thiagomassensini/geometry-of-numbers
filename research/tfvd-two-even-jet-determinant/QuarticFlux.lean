import CompletedTraceJets

namespace CarryTwoEvenJets
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Four independent inputs are retained before specializing to a determinant. -/
theorem polarizedQuartic_add_four (a b c d e f g h : Fin 4 → ℂ) :
    polarizedQuartic (a+e) (b+f) (c+g) (d+h) =
      polarizedQuartic a b c d + polarizedQuartic a b c h +
      polarizedQuartic a b g d + polarizedQuartic a b g h +
      polarizedQuartic a f c d + polarizedQuartic a f c h +
      polarizedQuartic a f g d + polarizedQuartic a f g h +
      polarizedQuartic e b c d + polarizedQuartic e b c h +
      polarizedQuartic e b g d + polarizedQuartic e b g h +
      polarizedQuartic e f c d + polarizedQuartic e f c h +
      polarizedQuartic e f g d + polarizedQuartic e f g h := by
  simp only [polarizedQuartic,Pi.add_apply]
  ring

/-- Exact discrete product rule in four slots: each later slot is still
recombined. Expanding them recovers all FIFTEEN non-head-only sectors. -/
def quarticFlux (a e : Fin 4 → ℂ) : ℂ :=
  polarizedQuartic e (a+e) (a+e) (a+e)+
  polarizedQuartic a e (a+e) (a+e)+
  polarizedQuartic a a e (a+e)+
  polarizedQuartic a a a e

theorem quartic_add_flux (a e : Fin 4 → ℂ) :
    quartic (a+e) = quartic a+quarticFlux a e := by
  simp only [quartic,quarticFlux,polarizedQuartic,Pi.add_apply]
  ring

/-- Finite summation of the exact discrete product rule. This is a cutoff
identity applied below to the native TFVD cells, not an isometry assertion. -/
theorem quartic_prefix_flux (p c : ℕ → (Fin 4 → ℂ))
    (hc : ∀ m, p (m+1)=p m+c m) (M : ℕ) :
    quartic (p M) = quartic (p 0)+∑ m ∈ Finset.range M, quarticFlux (p m) (c m) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [hc,quartic_add_flux,ih,Finset.sum_range_succ]
    ring

/-- The two original value/log tails enter the full trace, and only then
are their even jets observed in this remainder. -/
def determinantTail (M : ℕ) : ℂ := quarticFlux (headEvenJets M) (tailEvenJets M)

/-- The source-specific prefix law: ordinary cells, fixed completion, actual seed. -/
theorem native_prefix_flux (M : ℕ) :
    quartic (headEvenJets M) = quartic (headEvenJets 0)+
      ∑ m ∈ Finset.range M, quarticFlux (headEvenJets m) (cellEvenJets m) :=
  quartic_prefix_flux headEvenJets cellEvenJets head_even_jets_succ M

/-- Main joint identity for the exact canonical H2 determinant. NO head
inverse occurs. The complete F0 factor is common to the entire ledger. -/
theorem native_two_even_tfvd_ledger (M : ℕ) :
    (nativeEvenJets 0)^4 *
      (((canonicalCompletedNativeLogDerivativeMoment 0 : ℝ)*canonicalCompletedNativeLogDerivativeMoment 2-
        (canonicalCompletedNativeLogDerivativeMoment 1)^2 : ℝ) : ℂ) =
      quartic (headEvenJets 0)+
      (∑ m ∈ Finset.range M, quarticFlux (headEvenJets m) (cellEvenJets m))+
      determinantTail M := by
  rw [native_two_even_determinant_clear,full_even_jets_head_tail M,quartic_add_flux,
    native_prefix_flux]
  rfl

/-- Exact remainder between two material cutoffs. It is the same joint
quantity, so a contribution cannot be kept in the prefix and dropped in the tail. -/
theorem determinantTail_step (M : ℕ) :
    determinantTail M = quarticFlux (headEvenJets M) (cellEvenJets M)+determinantTail (M+1) := by
  have h0 := native_two_even_tfvd_ledger M
  have h1 := native_two_even_tfvd_ledger (M+1)
  rw [Finset.sum_range_succ] at h1
  linear_combination h1-h0

/-- PR41's residual is tested in its original coefficients, before any
assumption about its sign. This algebraic completion does not require h0≠0. -/
theorem native_two_even_residual (a : ℝ) :
    quartic nativeEvenJets = (nativeEvenJets 0)^4 *
      (((canonicalCompletedNativeLogDerivativeMoment 0 *
        (canonicalCompletedNativeLogDerivativeMoment 2-2*a*canonicalCompletedNativeLogDerivativeMoment 1+
          a^2*canonicalCompletedNativeLogDerivativeMoment 0)-
        (a*canonicalCompletedNativeLogDerivativeMoment 0-canonicalCompletedNativeLogDerivativeMoment 1)^2 : ℝ) : ℂ)) := by
  rw [← native_two_even_determinant_clear]
  push_cast
  ring

/-- Only the old scalar prefix is required nonzero for the critical direction. -/
theorem native_two_even_critical_residual
    (hne : canonicalCompletedNativeLogDerivativeMoment 0 ≠ 0) :
    quartic nativeEvenJets = (nativeEvenJets 0)^4 *
      (((canonicalCompletedNativeLogDerivativeMoment 0 *
        (canonicalCompletedNativeLogDerivativeMoment 2-
          (canonicalCompletedNativeLogDerivativeMoment 1)^2/canonicalCompletedNativeLogDerivativeMoment 0) : ℝ) : ℂ)) := by
  rw [← native_two_even_determinant_clear]
  congr 1
  congr 1
  field_simp


end
end CarryTwoEvenJets
