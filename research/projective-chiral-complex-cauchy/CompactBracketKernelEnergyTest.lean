import CPFormal.Genuine.CpFiniteChart
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

end
end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.no_unrestricted_C3_chart_gradient_coercivity
#print axioms CPFormal.Analytic.Cp.compactBracketKernelEdgeEnergy_three_eq_six
#print axioms CPFormal.Analytic.Cp.compactBracketKernelSample_chart_zero
#print axioms CPFormal.Analytic.Cp.compactBracketKernelSample_first_edge_ne_zero
