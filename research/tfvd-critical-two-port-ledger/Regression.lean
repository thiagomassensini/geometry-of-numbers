import HeadCancellation

open CarryTfvdCritical CarrySelfAdjointOperator
open CarrySelfAdjointOperator.PhysicalSewing CarryConservativeIntertwiner
open scoped BigOperators Matrix ComplexConjugate
noncomputable section

-- The inherited odd phase is retained: a real odd jet has an imaginary material profile.
example (k : ℕ) : fixedMaterial 1 k firstOddBoundary =
    ![Complex.I*((k : ℂ)+1),-Complex.I*((k : ℂ)+1)] := by
  have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : physicalEndpointJetInput 2 k
      (![Complex.I*((k : ℂ)+1),-Complex.I*((k : ℂ)+1)] : Fin 2 → ℂ) = firstOddBoundary := by
    ext a
    fin_cases a <;> simp [physicalEndpointJetInput_finite,Fin.sum_univ_two,endpointGauge,
      nativeSourceJetOrderPhase,firstOddBoundary,canonicalCompletedC3RadialSecondStep,
      canonicalGreenJetStep]
    field_simp
    simp [Complex.I_sq]
  unfold fixedMaterial
  rw [← he,decodedEndpointCoefficients_encode]

-- Exact second-even profile with an arbitrary lower coefficient, before supplying any moments.
example (k : ℕ) (a : ℂ) : fixedMaterial 2 k (![a,0,-1,0] : Fin 4 → ℂ) =
    ![a-((k : ℂ)+1)^2/2,((k : ℂ)+1)^2,-((k : ℂ)+1)^2/2,0] := by
  have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : physicalEndpointJetInput 4 k
      (![a-((k : ℂ)+1)^2/2,((k : ℂ)+1)^2,-((k : ℂ)+1)^2/2,0] : Fin 4 → ℂ) = ![a,0,-1,0] := by
    ext r
    fin_cases r <;> simp [physicalEndpointJetInput_finite,Fin.sum_univ_succ,endpointGauge,
      nativeSourceJetOrderPhase,canonicalCompletedC3RadialSecondStep,canonicalGreenJetStep]
    all_goals field_simp
    all_goals try simp [Complex.I_sq]
    all_goals ring
    all_goals simp only [or_true]
  unfold fixedMaterial
  rw [← he,decodedEndpointCoefficients_encode]
