import CPFormal.Genuine.CpFiniteChart
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import Mathlib.Tactic

/-! Exact finite-support diagnostic: a genuine C3 bracket-kernel sample
can carry a nonzero Dirichlet edge. It is not a native eigenwave. -/

open scoped BigOperators
namespace CPFormal.Analytic.Cp

noncomputable section

def compactBracketKernelSample (n : ℤ) : ℂ :=
  if n = 2 then 2 else if n = 3 then 1 else 0

private theorem offsets_three :
    CPFormal.Genuine.Cp.balancedOffsets 3 = {(-1 : ℤ), 1} := by
  decide

private theorem compactBracketKernelSample_far
    {n : ℤ} (hn : 4 ≤ n) :
    compactBracketKernelSample n = 0 := by
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  simp [compactBracketKernelSample, h2, h3]

theorem compactBracketKernelSample_bracket_zero (k : ℕ) :
    CPFormal.Genuine.Cp.bracket 3 compactBracketKernelSample
      (CPFormal.Genuine.Cp.alignedCenter 3 k) = 0 := by
  cases k with
  | zero =>
      norm_num [CPFormal.Genuine.Cp.bracket, CPFormal.Genuine.Cp.legSum,
        offsets_three, CPFormal.Genuine.Cp.alignedCenter,
        compactBracketKernelSample]
  | succ k =>
      have hcenter : (5 : ℤ) ≤
          CPFormal.Genuine.Cp.alignedCenter 3 (k+1) - 1 := by
        simp [CPFormal.Genuine.Cp.alignedCenter]
        omega
      have hl : compactBracketKernelSample
          (CPFormal.Genuine.Cp.alignedCenter 3 (k+1) - 1) = 0 :=
        compactBracketKernelSample_far (by omega)
      have hm : compactBracketKernelSample
          (CPFormal.Genuine.Cp.alignedCenter 3 (k+1)) = 0 :=
        compactBracketKernelSample_far (by omega)
      have hr : compactBracketKernelSample
          (CPFormal.Genuine.Cp.alignedCenter 3 (k+1) + 1) = 0 :=
        compactBracketKernelSample_far (by omega)
      have hl' : compactBracketKernelSample
          (CPFormal.Genuine.Cp.alignedCenter 3 (k+1) + (-1)) = 0 := by
        simpa [sub_eq_add_neg] using hl
      simp [CPFormal.Genuine.Cp.bracket, CPFormal.Genuine.Cp.legSum,
        offsets_three, hl', hm, hr]

theorem compactBracketKernelSample_chart_zero (M : ℕ) :
    CPFormal.Genuine.Cp.finiteChart 3 M compactBracketKernelSample = 0 := by
  simp [CPFormal.Genuine.Cp.finiteChart,
    CPFormal.Genuine.Cp.seedSum, compactBracketKernelSample_bracket_zero,
    CPFormal.Genuine.Cp.halfRange, compactBracketKernelSample]

/-- The same state has a nonzero first Dirichlet edge despite perfect
C3 bracket closure for every cutoff. -/
theorem compactBracketKernelSample_first_edge_ne_zero :
    compactBracketKernelSample 2 - compactBracketKernelSample 1 ≠ 0 := by
  norm_num [compactBracketKernelSample]

/-- Sum of squared ordinary adjacent differences on the first N edges. -/
def compactBracketKernelEdgeEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    Complex.normSq
      (compactBracketKernelSample ((n : ℤ) + 2) -
        compactBracketKernelSample ((n : ℤ) + 1))

/-- Exact finite positive bulk, despite zero finite Cp charts for ALL cuts. -/
theorem compactBracketKernelEdgeEnergy_three_eq_six :
    compactBracketKernelEdgeEnergy 3 = 6 := by
  norm_num [compactBracketKernelEdgeEnergy, Finset.sum_range_succ,
    compactBracketKernelSample]

/-- No uniform scalar C3-chart coercivity of the genuine gradient energy
is possible on arbitrary sample fields, even for the very first block.
A restricted theorem for the native eigenwave class would require ADDITIONAL
structure; this negative result does not concern Genuine zeros directly. -/
theorem no_unrestricted_C3_chart_gradient_coercivity :
    ¬ ∃ C : ℝ, ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.range 3,
        Complex.normSq (f ((n : ℤ) + 2) - f ((n : ℤ) + 1))) ≤
        C * Complex.normSq (CPFormal.Genuine.Cp.finiteChart 3 1 f) := by
  rintro ⟨C, h⟩
  have htoy := h compactBracketKernelSample
  have henergy := compactBracketKernelEdgeEnergy_three_eq_six
  dsimp [compactBracketKernelEdgeEnergy] at henergy
  rw [henergy, compactBracketKernelSample_chart_zero] at htoy
  norm_num at htoy

/-- Original first three ordinary edge differences of the compact
C3-kernel sample, as an actual finite native TFVD edge state. -/
def compactC3KernelGradientCore : NativeGpreComplexEdgeCore :=
  Finsupp.single 0 (2 : ℂ) +
    Finsupp.single 1 (-1 : ℂ) +
      Finsupp.single 2 (-1 : ℂ)

/-- The three native core coordinates are LITERALLY the ordinary forward
differences of the arithmetic C3-bracket-kernel sample. -/
theorem compactC3KernelGradientCore_eq_sample_differences
    {n : ℕ} (hn : n < 3) :
    compactC3KernelGradientCore n =
      compactBracketKernelSample ((n : ℤ) + 2) -
        compactBracketKernelSample ((n : ℤ) + 1) := by
  interval_cases n <;>
    norm_num [compactC3KernelGradientCore, compactBracketKernelSample,
      Finsupp.single_apply]

/-- Faithful TFVD reconstruction preserves all six energy units even
though the arithmetic C3 chart of the underlying sample is ZERO. -/
theorem compactC3Kernel_reconstructedTfvd_energy_eq_six
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (∑ n ∈ Finset.range 3,
      Complex.normSq
        ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S
            (nativeGpreCanonicalVerticalRealization compactC3KernelGradientCore))) n)) =
      6 := by
  have hpoint (n : ℕ) :
      (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (nativeGpreFiniteTfvdAnalysis q S
          (nativeGpreCanonicalVerticalRealization compactC3KernelGradientCore))) n =
      compactC3KernelGradientCore n := by
    rw [nativeGpreFiniteTfvdReconstruction_analysis
      q hqpos hq1 S (nativeGpreCanonicalVerticalRealization compactC3KernelGradientCore)]
    rfl
  simp_rw [hpoint]
  norm_num [compactC3KernelGradientCore, Finset.sum_range_succ,
    Finsupp.single_apply]

/-- The sharp mismatch: the C3 chart of the original sample vanishes at
every cutoff, while its reconstructed ordinary gradient state has energy 6. -/
theorem compactC3Kernel_tfvd_no_scalar_energy_collapse
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (∀ M : ℕ,
      CPFormal.Genuine.Cp.finiteChart 3 M compactBracketKernelSample = 0) ∧
      (∑ n ∈ Finset.range 3,
        Complex.normSq
          ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S
              (nativeGpreCanonicalVerticalRealization compactC3KernelGradientCore))) n)) =
        6 := by
  exact ⟨compactBracketKernelSample_chart_zero,
    compactC3Kernel_reconstructedTfvd_energy_eq_six q hqpos hq1 S⟩

end
end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.compactC3Kernel_tfvd_no_scalar_energy_collapse
#print axioms CPFormal.Analytic.Cp.compactC3Kernel_reconstructedTfvd_energy_eq_six
#print axioms CPFormal.Analytic.Cp.no_unrestricted_C3_chart_gradient_coercivity
#print axioms CPFormal.Analytic.Cp.compactBracketKernelEdgeEnergy_three_eq_six
#print axioms CPFormal.Analytic.Cp.compactBracketKernelSample_chart_zero
#print axioms CPFormal.Analytic.Cp.compactBracketKernelSample_first_edge_ne_zero
