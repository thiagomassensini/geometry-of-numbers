#!/usr/bin/env python3
"""Generate Lean exact rational checks from the six-order 4096-arc Arb export."""

import json
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
INPUT = HERE / "evidence" / "C3_ARb_RESIDUAL_ARCS_4096.json"
AGGREGATE_INPUT = HERE / "evidence" / "C3_ARb_RESIDUALS_4096.json"
OUTPUT = HERE.parent / "SigmaContour51ArbArcSumCertificate4096.lean"
PREFIX = "contour51Arb4096"
ARC_COUNT = 4096
MAX_N = 5


def lean_rat(value: str) -> str:
    q = Fraction(value)
    numerator = f"({q.numerator} : ℚ)"
    return numerator if q.denominator == 1 else f"{numerator} / {q.denominator}"


def list_block(name: str, values: list[str]) -> str:
    lines = [f"def {name} : List ℚ := ["]
    for start in range(0, len(values), 8):
        row = ", ".join(lean_rat(value) for value in values[start : start + 8])
        lines.append("  " + row + ("," if start + 8 < len(values) else ""))
    lines.append("]")
    return "\n".join(lines)


def main() -> None:
    data = json.loads(INPUT.read_text(encoding="utf-8"))
    if data["arcs"] != ARC_COUNT:
        raise ValueError(f"expected a {ARC_COUNT}-arc certificate")
    if len(data["intervals"]) != ARC_COUNT or len(data["weighted_sums"]) < MAX_N + 1:
        raise ValueError("arc or residual count does not match the expected six-order export")

    blocks = [
        "import Mathlib.Tactic",
        "",
        "namespace CarrySigmaObstruction",
        "",
        "noncomputable section",
        "set_option maxRecDepth 16384",
        "set_option maxHeartbeats 1000000000",
        "",
        "/-- Outward rational lower endpoints for each complete 4096-arc Arb range. -/",
    ]
    sums_by_order = {row["n"]: row for row in data["weighted_sums"]}
    recorded_by_order = {
        row["n"]: row for row in json.loads(AGGREGATE_INPUT.read_text(encoding="utf-8"))["residuals"]
    }
    for n in range(MAX_N + 1):
        lower = [row["residual_ranges"][n]["lower"] for row in data["intervals"]]
        upper = [row["residual_ranges"][n]["upper"] for row in data["intervals"]]
        lower_name = f"{PREFIX}LowerArcRanges{n}"
        upper_name = f"{PREFIX}UpperArcRanges{n}"
        blocks.append(list_block(lower_name, lower))
        blocks.append("")
        blocks.append("/-- Outward rational upper endpoints for each complete 4096-arc Arb range. -/")
        blocks.append(list_block(upper_name, upper))
        blocks.append("")
        lower_sum_name = f"{PREFIX}WeightedLower{n}"
        upper_sum_name = f"{PREFIX}WeightedUpper{n}"
        blocks.append(f"def {lower_sum_name} : ℚ := (1 / {ARC_COUNT} : ℚ) * {lower_name}.sum")
        blocks.append(f"def {upper_sum_name} : ℚ := (1 / {ARC_COUNT} : ℚ) * {upper_name}.sum")
        blocks.append("")

        recorded = recorded_by_order[n]
        blocks.append(
            f"def {PREFIX}RecordedLower{n} : ℚ := "
            f"{lean_rat(recorded['residual_lower'])}"
        )
        blocks.append(
            f"def {PREFIX}RecordedUpper{n} : ℚ := "
            f"{lean_rat(recorded['residual_upper'])}"
        )
        blocks.append(
            f"theorem {lower_sum_name}_eq_exported : {lower_sum_name} = "
            f"{lean_rat(sums_by_order[n]['lower'])} := by\n"
            f"  norm_num [{lower_sum_name}, {lower_name}]"
        )
        blocks.append(
            f"theorem {upper_sum_name}_eq_exported : {upper_sum_name} = "
            f"{lean_rat(sums_by_order[n]['upper'])} := by\n"
            f"  norm_num [{upper_sum_name}, {upper_name}]"
        )
        blocks.append("")

        # A total-list identity makes the evaluator ranges addressable by natural arc index.
        blocks.append(f"def {PREFIX}LowerArcEndpoint{n} (k : ℕ) : ℚ := {lower_name}.getD k 0")
        blocks.append(f"def {PREFIX}UpperArcEndpoint{n} (k : ℕ) : ℚ := {upper_name}.getD k 0")
        blocks.append(f"theorem {PREFIX}LowerArcRanges{n}_length : {lower_name}.length = {ARC_COUNT} := by norm_num [{lower_name}]")
        blocks.append(f"theorem {PREFIX}UpperArcRanges{n}_length : {upper_name}.length = {ARC_COUNT} := by norm_num [{upper_name}]")
        blocks.append("")

    blocks.extend(
        [
            "/-- The exact per-arc sums enclose the recorded aggregate Arb intervals for the first three residuals. This is rational arithmetic only; it does not prove per-arc evaluator inclusion. -/",
            "theorem contour51Arb4096FirstThreeWeightedRecordedBounds :",
            "    contour51Arb4096RecordedLower0 ≤ contour51Arb4096WeightedLower0 ∧",
            "    contour51Arb4096WeightedUpper0 ≤ contour51Arb4096RecordedUpper0 ∧",
            "    contour51Arb4096RecordedLower1 ≤ contour51Arb4096WeightedLower1 ∧",
            "    contour51Arb4096WeightedUpper1 ≤ contour51Arb4096RecordedUpper1 ∧",
            "    contour51Arb4096RecordedLower2 ≤ contour51Arb4096WeightedLower2 ∧",
            "    contour51Arb4096WeightedUpper2 ≤ contour51Arb4096RecordedUpper2 := by",
            "  norm_num [",
            "    contour51Arb4096WeightedLower0_eq_exported, contour51Arb4096WeightedUpper0_eq_exported,",
            "    contour51Arb4096WeightedLower1_eq_exported, contour51Arb4096WeightedUpper1_eq_exported,",
            "    contour51Arb4096WeightedLower2_eq_exported, contour51Arb4096WeightedUpper2_eq_exported,",
            "    contour51Arb4096RecordedLower0, contour51Arb4096RecordedUpper0,",
            "    contour51Arb4096RecordedLower1, contour51Arb4096RecordedUpper1,",
            "    contour51Arb4096RecordedLower2, contour51Arb4096RecordedUpper2]",
            "",
            "/-- Exact rational enclosure comparisons for all six exported residual intervals. -/",
            "theorem contour51Arb4096AllSixWeightedRecordedBounds :",
        ]
    )
    all_six_bounds: list[str] = []
    all_six_definitions: list[str] = []
    for n in range(6):
        all_six_bounds.extend(
            [
                f"    contour51Arb4096RecordedLower{n} ≤ contour51Arb4096WeightedLower{n}",
                f"    contour51Arb4096WeightedUpper{n} ≤ contour51Arb4096RecordedUpper{n}",
            ]
        )
        all_six_definitions.extend(
            [
                f"contour51Arb4096WeightedLower{n}_eq_exported",
                f"contour51Arb4096WeightedUpper{n}_eq_exported",
                f"contour51Arb4096RecordedLower{n}",
                f"contour51Arb4096RecordedUpper{n}",
            ]
        )
    for index in range(len(all_six_bounds) - 1):
        all_six_bounds[index] += " ∧"
    all_six_bounds[-1] += " := by"
    blocks.extend(all_six_bounds)
    blocks.append("  norm_num [")
    for start in range(0, len(all_six_definitions), 2):
        group = ", ".join(all_six_definitions[start : start + 2])
        suffix = "," if start + 2 < len(all_six_definitions) else "]"
        blocks.append("    " + group + suffix)
    blocks.extend(
        [
            "",
            "#print axioms contour51Arb4096WeightedLower0_eq_exported",
            "#print axioms contour51Arb4096WeightedUpper0_eq_exported",
            "#print axioms contour51Arb4096WeightedLower1_eq_exported",
            "#print axioms contour51Arb4096WeightedUpper1_eq_exported",
            "#print axioms contour51Arb4096WeightedLower2_eq_exported",
            "#print axioms contour51Arb4096WeightedUpper2_eq_exported",
            "#print axioms contour51Arb4096FirstThreeWeightedRecordedBounds",
            "#print axioms contour51Arb4096AllSixWeightedRecordedBounds",
            "",
            "end",
            "end CarrySigmaObstruction",
            "",
        ]
    )
    OUTPUT.write_text("\n\n".join(blocks).rstrip() + "\n", encoding="utf-8")
    print(f"generated {OUTPUT}")


if __name__ == "__main__":
    main()
