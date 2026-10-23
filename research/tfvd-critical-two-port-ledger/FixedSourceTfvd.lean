import TwoPortCorrection

namespace CarryTfvdCritical
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- x is FIXED as k varies; this is the independently prescribed endpoint decoder. -/
def fixedMaterial (n k : ℕ) (x : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  decodedEndpointCoefficients (2*n) k x

def canonicalStates (M n k : ℕ) : Fin (2*n) → CanonicalC3BracketTfvdCompletionState M :=
  fun j => canonicalC3BracketTfvdCompletionState M
    (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))

def fullSecond (M n k : ℕ) (x : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  tfvdMaterialSecondCoefficients (2*n) M k (fixedMaterial n k x) (canonicalStates M n k)

def headSecond (M n k : ℕ) (x : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  fun j => tfvdStateHeadResponse (canonicalCompletedC3RadialTiltPoint k j)
    (canonicalStates M n k j) * fixedMaterial n k x j

def errorSecond (M n k : ℕ) (x : Fin (2*n) → ℂ) :=
  fullSecond M n k x - headSecond M n k x

def fullSource (M n k : ℕ) (x : Fin (2*n) → ℂ) :=
  twoPortSynthesis (2*n) k (fixedMaterial n k x) (fullSecond M n k x)

def headSource (M n k : ℕ) (x : Fin (2*n) → ℂ) :=
  twoPortSynthesis (2*n) k (fixedMaterial n k x) (headSecond M n k x)

def headFlux (M n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  portFlux (2*n) k (fixedMaterial n k x) (headSecond M n k x)

def correctionFlux (M n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  portFlux (2*n) k (fixedMaterial n k x) (errorSecond M n k x)

theorem head_plus_error (M n k : ℕ) (x : Fin (2*n) → ℂ) :
    headSecond M n k x + errorSecond M n k x = fullSecond M n k x := by
  unfold errorSecond
  abel

/-- Full vector identity before pairing; finite cutoff is arbitrary because both tails remain. -/
theorem fullSource_eq_original (M n k : ℕ) (x : Fin (2*n) → ℂ)
    (hs : ∀ j : Fin (2*n), operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip)
    (hr : ∀ j : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    fullSource M n k x = nativeSourceProjectiveBoundaryJetSynthesis n k x := by
  change tfvdMaterialWholeSource (2*n) M k (fixedMaterial n k x) (canonicalStates M n k) = _
  unfold canonicalStates
  rw [tfvdMaterialWholeSource_canonical (2*n) M k (fixedMaterial n k x) hs hr]
  rw [← physicalEndpointJetInput_wholeSource n k (fixedMaterial n k x)]
  unfold fixedMaterial
  rw [physicalEndpointJetInput_decode]

/-- The same eventual regular section works for ALL exact TFVD cutoffs and all fixed inputs. -/
theorem fullSource_eventually_eq_original (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, ∀ x : Fin (2*n) → ℂ,
      fullSource M n k x = nativeSourceProjectiveBoundaryJetSynthesis n k x := by
  filter_upwards [CarryRadialConservative.finite_eventually_admissible (2*n)] with k hk M x
  apply fullSource_eq_original M n k x
  · intro j
    exact (hk j).1
  · intro j
    exact (hk j).2

/-- Independent source inputs and independent TFVD cutoffs; no mixed sector is discarded. -/
theorem full_head_polarized_ledger (M L n k : ℕ) (x y : Fin (2*n) → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm (fullSource M n k x) (fullSource L n k y) -
      canonicalCompletedNativeProjectiveChiralForm (headSource M n k x) (headSource L n k y) =
    (Complex.I*((k : ℂ)+1)/2) *
      (matrixPairing (cauchyMatrix (2*n)) (errorSecond M n k x) (fixedMaterial n k y) -
        matrixPairing (cauchyMatrix (2*n)) (fixedMaterial n k x) (errorSecond L n k y)) := by
  have he := secondPort_pairing_change (2*n) k (fixedMaterial n k x) (headSecond M n k x)
    (fixedMaterial n k y) (headSecond L n k y) (errorSecond M n k x) (errorSecond L n k y)
  rw [head_plus_error,head_plus_error] at he
  exact he

theorem full_head_real_ledger (M n k : ℕ) (x : Fin (2*n) → ℂ) :
    (canonicalCompletedNativeProjectiveChiralForm (fullSource M n k x) (fullSource M n k x)).re =
      headFlux M n k x + correctionFlux M n k x := by
  unfold fullSource
  rw [twoPort_real_self, ← head_plus_error M n k x, portFlux_add]
  rfl

/-- The ratio error is evaluated with the original two tails and full denominators. -/
theorem errorSecond_determinant (M n k : ℕ) (x : Fin (2*n) → ℂ)
    (hQ : ∀ j : Fin (2*n), cpChartFactor 3 (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) ≠ 0)
    (hXi : ∀ j : Fin (2*n), nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hT : ∀ j : Fin (2*n), (canonicalStates M n k j).valueReadout ≠ 0)
    (hH : ∀ j : Fin (2*n), (canonicalStates M n k j).transport.valueReadout ≠ 0) :
    errorSecond M n k x = fun j =>
      (Complex.I * ((canonicalStates M n k j).transport.valueReadout * (canonicalStates M n k j).logJetTail -
        (canonicalStates M n k j).transport.logJetReadout * (canonicalStates M n k j).valueTail) /
        ((canonicalStates M n k j).transport.valueReadout * (canonicalStates M n k j).valueReadout)) *
      fixedMaterial n k x j := by
  funext j
  unfold errorSecond fullSecond headSecond
  simp only [Pi.sub_apply,tfvdMaterialSecondCoefficients]
  rw [← sub_mul,tfvdStateHeadTail_responseDefect _ (canonicalStates M n k j) (hQ j) (hXi j) (hT j) (hH j)]
  rfl

theorem exact_ratio_denominators_eventually (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, ∀ j : Fin (2*n),
      cpChartFactor 3 (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) ≠ 0 ∧
      nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      (canonicalStates M n k j).valueReadout ≠ 0 := by
  filter_upwards [CarryRadialConservative.finite_eventually_admissible (2*n)] with k hk M j
  exact tfvdCanonicalResponse_regular_denominators M _ (hk j).1 (hk j).2.1

end
end CarryTfvdCritical
