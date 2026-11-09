#!/usr/bin/env python3
"""Export the 512 outward Arb response bounds as a Lean rational table."""

import csv
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CSV_INPUT = HERE / "evidence" / "C3_ARb_ARCS.csv"
LEAN_OUTPUT = ROOT / "SigmaContour51ArbBoundCertificate512.lean"
ARC_COUNT = 512
SIMPLE_BOUND = Fraction(746413, 1_000_000)


def outward_upper(value: str) -> Fraction:
    """Convert Arb's displayed ball to its exact outward rational upper endpoint."""
    endpoint = arb(value).upper()
    midpoint, radius, exponent = endpoint.mid_rad_10exp()
    exponent = int(exponent)
    scale = Fraction(10**exponent, 1) if exponent >= 0 else Fraction(1, 10 ** (-exponent))
    return Fraction(int(midpoint)) * scale + Fraction(int(radius)) * scale


def lean_rat(q: Fraction) -> str:
    numerator = f"({q.numerator} : ℚ)"
    return numerator if q.denominator == 1 else f"{numerator} / {q.denominator}"


def main() -> None:
    ctx.prec = 160
    with CSV_INPUT.open(newline="", encoding="utf-8") as source:
        rows = list(csv.DictReader(source))
    if len(rows) != ARC_COUNT or [int(row["index"]) for row in rows] != list(range(ARC_COUNT)):
        raise ValueError("expected the ordered 512-arc C3 certificate")

    upper = [outward_upper(row["response_upper"]) for row in rows]
    if max(upper) > SIMPLE_BOUND or SIMPLE_BOUND >= Fraction(4, 5):
        raise ArithmeticError("the rational response bound does not clear 4/5")

    lines = [
        "import SigmaContour51SourceTail",
        "import SigmaContour51ArbContourBridge",
        "import Mathlib.Tactic",
        "",
        "namespace CarrySigmaObstruction",
        "",
        "noncomputable section",
        "set_option maxRecDepth 16384",
        "set_option maxHeartbeats 1000000000",
        "",
        "/-- Exact outward rational upper endpoints exported from the 512-arc Arb response certificate. -/",
        "def contour51Arb512ResponseUpperBounds : List ℚ := [",
    ]
    for start in range(0, ARC_COUNT, 8):
        values = ", ".join(lean_rat(q) for q in upper[start : start + 8])
        lines.append("  " + values + ("," if start + 8 < ARC_COUNT else ""))
    lines.extend(
        [
            "]",
            "",
            "/-- Total lookup for a response bound at an arc index. -/",
            "def contour51Arb512ResponseUpperBound (k : ℕ) : ℚ :=",
            "  contour51Arb512ResponseUpperBounds.getD k 0",
            "",
            "theorem contour51Arb512ResponseUpperBounds_length :",
            "    contour51Arb512ResponseUpperBounds.length = 512 := by",
            "  norm_num [contour51Arb512ResponseUpperBounds]",
            "",
            "/-- Every exported Arb response endpoint is at most the simple rational bound. -/",
            "theorem contour51Arb512ResponseUpperBounds_all_le_simple :",
            "    ∀ q ∈ contour51Arb512ResponseUpperBounds, q ≤ (746413 / 1000000 : ℚ) := by",
            "  simp only [contour51Arb512ResponseUpperBounds, List.forall_mem_cons]",
            "  norm_num",
            "",
            "/-- The indexed endpoint inherits the checked list bound by list membership. -/",
            "theorem contour51Arb512ResponseUpperBound_le_simple (k : ℕ) (hk : k < 512) :",
            "    contour51Arb512ResponseUpperBound k ≤ (746413 / 1000000 : ℚ) := by",
            "  have hmem : contour51Arb512ResponseUpperBound k ∈ contour51Arb512ResponseUpperBounds := by",
            "    change contour51Arb512ResponseUpperBounds.getD k 0 ∈ contour51Arb512ResponseUpperBounds",
            "    apply (List.mem_iff_getElem).2",
            "    have hkLen : k < contour51Arb512ResponseUpperBounds.length := by",
            "      simpa [contour51Arb512ResponseUpperBounds_length] using hk",
            "    refine ⟨k, hkLen, ?_⟩",
            "    exact List.getElem_eq_getD (h := hkLen) 0",
            "  simpa [contour51Arb512ResponseUpperBound] using",
            "    contour51Arb512ResponseUpperBounds_all_le_simple _ hmem",
            "",
            "theorem contour51Arb512ResponseUpperBound_lt_four_fifths (k : ℕ)",
            "    (hk : k < 512) : contour51Arb512ResponseUpperBound k < (4 / 5 : ℚ) := by",
            "  have h := contour51Arb512ResponseUpperBound_le_simple k hk",
            "  norm_num at h ⊢",
            "  exact lt_of_le_of_lt h (by norm_num)",
            "",
            "/-- Exact lower-semicircle parameter interval of arc `k` in Arb's 512-arc partition. -/",
            "def contour51Arb512ParameterArc (k : ℕ) : Set ℝ :=",
            "  Set.Icc ((k : ℝ) / 512) (((k + 1 : ℕ) : ℝ) / 512)",
            "",
            "/-- The unresolved analytic inclusion for C3: on every complete parameter arc,",
            "the original source response is below the corresponding outward Arb endpoint. -/",
            "def contour51Arb512ResponseArcEvaluatorInclusion : Prop :=",
            "  ∀ k : ℕ, k < 512 → ∀ u : ℝ, u ∈ contour51Arb512ParameterArc k →",
            "    ‖contour51OriginalResponse (circleMap 0 51 (-Real.pi * u))‖ ≤",
            "      contour51Arb512ResponseUpperBound k",
            "",
            "/-- Every point of `[0,1]` belongs to a closed cell of the rational 512-arc partition. -/",
            "theorem contour51Arb512ParameterArc_cover (u : ℝ)",
            "    (hu : u ∈ Set.Icc (0 : ℝ) 1) :",
            "    ∃ k : ℕ, k < 512 ∧ u ∈ contour51Arb512ParameterArc k := by",
            "  rcases hu with ⟨hu0, hu1Bound⟩",
            "  by_cases hu1 : u = 1",
            "  · subst u",
            "    refine ⟨511, by norm_num, ?_⟩",
            "    norm_num [contour51Arb512ParameterArc]",
            "  · have huLt : u < 1 := lt_of_le_of_ne hu1Bound hu1",
            "    let k : ℕ := ⌊512 * u⌋₊",
            "    have hxnonneg : 0 ≤ 512 * u := mul_nonneg (by norm_num) hu0",
            "    have hkLo : (k : ℝ) ≤ u * 512 := by",
            "      simpa [k, mul_comm] using (Nat.floor_le hxnonneg)",
            "    have hkHi : u * 512 < (k : ℝ) + 1 := by",
            "      simpa [k, mul_comm] using (Nat.lt_floor_add_one (512 * u))",
            "    have hscaledLt : 512 * u < 512 := by nlinarith",
            "    have hk : k < 512 := (Nat.floor_lt hxnonneg).2 hscaledLt",
            "    refine ⟨k, hk, ?_⟩",
            "    rw [contour51Arb512ParameterArc, Set.mem_Icc]",
            "    constructor",
            "    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).2",
            "      exact hkLo",
            "    · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 512)).2",
            "      norm_num [Nat.cast_add] at hkHi ⊢",
            "      exact hkHi.le",
            "",
            "/-- The finite 512-arc evaluator inclusions imply the full uniform response bound",
            "on the lower semicircle. Every arc endpoint is checked against the rational Arb table. -/",
            "theorem contour51ArbLowerSemicircleUniformResponseBound_of_512_arc_evaluator_inclusion",
            "    (hArc : contour51Arb512ResponseArcEvaluatorInclusion) :",
            "    contour51ArbLowerSemicircleUniformResponseBound := by",
            "  intro u hu",
            "  obtain ⟨k, hk, huk⟩ := contour51Arb512ParameterArc_cover u hu",
            "  have hEval := hArc k hk u huk",
            "  have hUpper := contour51Arb512ResponseUpperBound_lt_four_fifths k hk",
            "  have hUpperR : (contour51Arb512ResponseUpperBound k : ℝ) < (4 / 5 : ℝ) := by",
            "    have hcast : ((contour51Arb512ResponseUpperBound k : ℚ) : ℝ) <",
            "        ((4 / 5 : ℚ) : ℝ) := (Rat.cast_lt).2 hUpper",
            "    simpa using hcast",
            "  exact hEval.trans hUpperR.le",
            "",
            "/-- Conditional full-circle C3 bound obtained from the complete 512-arc response",
            "inclusion and the already compiled exact lower-semicircle symmetry reduction. -/",
            "theorem contour51OriginalResponse_circle_norm_bound_of_512_arc_evaluator_inclusion",
            "    (hArc : contour51Arb512ResponseArcEvaluatorInclusion) :",
            "    ∀ z ∈ Metric.sphere (0 : ℂ) 51, ‖contour51OriginalResponse z‖ ≤ 4 / 5 := by",
            "  exact contour51OriginalResponse_circle_norm_bound_of_lower_semicircle_uniform_bound",
            "    (contour51ArbLowerSemicircleUniformResponseBound_of_512_arc_evaluator_inclusion hArc)",
            "",
            "/-- The 512-arc response inclusion supplies the analytic input to the existing",
            "all-window theorem; the six original residual signs remain an explicit premise. -/",
            "theorem completedNative_sigmaPadeD_pos_of_contour51_512_arc_inclusions",
            "    (hArc : contour51Arb512ResponseArcEvaluatorInclusion) :",
            "    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧",
            "      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧",
            "      (∀ i : Fin 10,",
            "        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧",
            "      ((∀ n : ℕ, n ≤ 5 → 0 ≤ completedNativeContour51Residual ts n) →",
            "        ∀ s : ℕ, 0 < CarrySigmaPade.sigmaPadeD 0 s) := by",
            "  apply completedNative_sigmaPadeD_pos_of_contour51_bound",
            "  intro z hz",
            "  have h := contour51OriginalResponse_circle_norm_bound_of_512_arc_evaluator_inclusion",
            "    hArc z hz",
            "  simpa [contour51OriginalResponse] using h",
            "",
            "#print axioms contour51ArbLowerSemicircleUniformResponseBound_of_512_arc_evaluator_inclusion",
            "#print axioms contour51OriginalResponse_circle_norm_bound_of_512_arc_evaluator_inclusion",
            "#print axioms completedNative_sigmaPadeD_pos_of_contour51_512_arc_inclusions",
            "",
            "end",
            "end CarrySigmaObstruction",
            "",
        ]
    )
    LEAN_OUTPUT.write_text("\n".join(lines), encoding="utf-8")
    print(f"arcs={len(upper)}")
    print(f"max_outward_response_upper={max(upper)}")
    print(f"simple_bound={SIMPLE_BOUND}")
    print(f"output={LEAN_OUTPUT}")


if __name__ == "__main__":
    main()
