import CutoffResidual

/-! Exact matrix of the ORIGINAL completion, on value/log-jet pairs.
The named coefficients expand the existing map; they are not free weights.
The radial/horizontal Green port is a different typed object and is not
silently substituted for these value/log-jet inputs. -/
namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

def valueGain (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z / cpChartFactor 3 (operatorHeightParameter z)

def jetGain (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z * Complex.I * cpChartFactor 3 (operatorHeightParameter z) /
    (cpChartFactor 3 (operatorHeightParameter z))^2

def companionShear (z : ℂ) : ℂ :=
  nativeXiCompletionBoundaryCompanion z / cpChartFactor 3 (operatorHeightParameter z) +
    nativeXiCompletionFactor z * Complex.I *
      deriv (cpChartFactor 3) (operatorHeightParameter z) /
        (cpChartFactor 3 (operatorHeightParameter z))^2

theorem native_completion_matrix (z : ℂ) (p : ℂ × ℂ) :
    nativeCompletionTrace z p =
      (valueGain z * p.1, companionShear z * p.1 + jetGain z * p.2) := by
  apply Prod.ext <;>
    simp only [nativeCompletionTrace, valueGain, companionShear, jetGain, div_eq_mul_inv]
  · ring
  · ring

theorem jet_gain_height_factor (z : ℂ) : jetGain z = Complex.I * valueGain z := by
  by_cases h : cpChartFactor 3 (operatorHeightParameter z) = 0
  · simp [jetGain, valueGain, h]
  · unfold jetGain valueGain
    field_simp

/-- The Gamma derivative is retained when completion acts on the literal
integral value/log-integral pair. -/
theorem integral_completion_matrix (z : ℂ) (p : ℂ × ℂ) :
    nativeCompletionTrace z (gammaUndress (operatorHeightParameter z) p) =
      (valueGain z / Complex.Gammaℝ (operatorHeightParameter z) * p.1,
       (companionShear z / Complex.Gammaℝ (operatorHeightParameter z) +
         jetGain z * deriv Complex.Gammaℝ (operatorHeightParameter z) /
           (Complex.Gammaℝ (operatorHeightParameter z))^2) * p.1 +
       jetGain z / Complex.Gammaℝ (operatorHeightParameter z) * p.2) := by
  rw [native_completion_matrix]
  apply Prod.ext <;> simp only [gammaUndress, div_eq_mul_inv] <;> ring

/-- Two independent correction channels, before their sum. The first is
forced by the height factor I; the second includes the camera derivative
and the ORIGINAL completion companion. -/
structure CompletionPairingChannels where
  jetTransport : ℂ
  companionTransport : ℂ

def CompletionPairingChannels.total (c : CompletionPairingChannels) : ℂ :=
  c.jetTransport + c.companionTransport

def completionPairingChannels (z w : ℂ) (p q : ℂ × ℂ) : CompletionPairingChannels where
  jetTransport :=
    (jetGain z * conj (valueGain w) - valueGain z * conj (jetGain w)) * p.1 * conj q.2
  companionTransport :=
    (companionShear z * conj (valueGain w) - valueGain z * conj (companionShear w)) *
      p.1 * conj q.1

/-- Exact polarized completion law, NOT a norm-preservation assertion. -/
theorem native_completion_pairing (z w : ℂ) (p q : ℂ × ℂ) :
    mixedScalarBoundaryWedge (nativeCompletionTrace z p).1 (nativeCompletionTrace z p).2
      (nativeCompletionTrace w q).1 (nativeCompletionTrace w q).2 =
      jetGain z * conj (valueGain w) * mixedScalarBoundaryWedge p.1 p.2 q.1 q.2 +
        (completionPairingChannels z w p q).total := by
  rw [native_completion_matrix, native_completion_matrix]
  simp only [mixedScalarBoundaryWedge, completionPairingChannels,
    CompletionPairingChannels.total, map_add, map_mul]
  ring

theorem completion_jet_transport_exact (z w : ℂ) (p q : ℂ × ℂ) :
    (completionPairingChannels z w p q).jetTransport =
      2 * Complex.I * valueGain z * conj (valueGain w) * p.1 * conj q.2 := by
  simp only [completionPairingChannels, jet_gain_height_factor, map_mul,
    Complex.conj_I]
  ring

/-- The height factor changes the antisymmetric raw pairing into a
symmetric mixed value/jet expression, plus the companion shear. -/
theorem native_completion_pairing_expanded (z w : ℂ) (p q : ℂ × ℂ) :
    mixedScalarBoundaryWedge (nativeCompletionTrace z p).1 (nativeCompletionTrace z p).2
      (nativeCompletionTrace w q).1 (nativeCompletionTrace w q).2 =
      Complex.I * valueGain z * conj (valueGain w) *
        (p.2 * conj q.1 + p.1 * conj q.2) +
      (companionShear z * conj (valueGain w) - valueGain z * conj (companionShear w)) *
        p.1 * conj q.1 := by
  rw [native_completion_pairing, CompletionPairingChannels.total,
    completion_jet_transport_exact]
  simp only [mixedScalarBoundaryWedge, completionPairingChannels, jet_gain_height_factor]
  ring

end
end CarryCompletedPairing
