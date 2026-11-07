#!/usr/bin/env python3
"""Instantiate the audited stage-18 proof pattern with stage-19 probe boxes."""

import re
from pathlib import Path

repo = Path(__file__).resolve().parents[6]
source = repo / "research/native-moving-schur-sigma/SigmaC5M2TaylorStateStage18Certificate.lean"
probe = Path(__file__).with_name("export-probe.log")
target = repo / "research/native-moving-schur-sigma/SigmaC5M2TaylorStateStage19Certificate.lean"

outputs = {}
for line in probe.read_text().splitlines():
    match = re.fullmatch(r"(power|term|sum)\.(lo|hi)=(.+)", line)
    if match:
        outputs.setdefault(match.group(1), {})[match.group(2)] = match.group(3)
if set(outputs) != {"power", "term", "sum"} or any(set(x) != {"lo", "hi"} for x in outputs.values()):
    raise SystemExit("probe log is incomplete")
if "BUILD_EXIT=0" not in probe.read_text():
    raise SystemExit("stage-19 export probe has no successful build marker")

text = source.read_text()
text = text.replace("Stage17", "__PREV__").replace("Stage18", "Stage19").replace("__PREV__", "Stage18")
text = text.replace("stage17", "__prev__").replace("stage18", "stage19").replace("__prev__", "stage18")
text = text.replace("355687428096000", "6402373705728000")
text = text.replace("Nat.factorial 17", "Nat.factorial 18")
text = text.replace("c5RoundedExpStateC 896 c5M2TaylorArgExport 18 = c5M2Stage19",
                    "c5RoundedExpStateC 896 c5M2TaylorArgExport 19 = c5M2Stage19")

old_sign_match = re.search(
    r"  have hleft : c5M2Stage18PowerReExport\.hi ≤ 0 := by\n.*?  rw \[c5IntervalMulNonpos _ _ hleft hright\]",
    text,
    re.S,
)
if not old_sign_match:
    raise SystemExit("could not locate the known stage-18 power sign block")
old_sign = old_sign_match.group(0)
hright_start = old_sign.index("  have hright :")
hright_end = old_sign.index("  rw [", hright_start)
hright = old_sign[hright_start:hright_end]
new_sign = (
    "  have hleft : 0 ≤ c5M2Stage18PowerReExport.lo := by\n"
    "    norm_num [c5M2Stage18PowerReExport]\n"
    + hright
    + "  rw [c5IntervalMulNonnegNonpos _ _ hleft hright]"
)
text = text[:old_sign_match.start()] + new_sign + text[old_sign_match.end():]

for part, val in outputs.items():
    name = {
        "power": "c5M2Stage19PowerReExport",
        "term": "c5M2Stage19TermReExport",
        "sum": "c5M2Stage19SumReExport",
    }[part]
    start = text.index(f"def {name} : Interval :=")
    end = text.find("\n\ndef ", start + 1)
    if end < 0:
        end = text.find("\n\ntheorem ", start + 1)
    lo, hi = val["lo"], val["hi"]
    replacement = f"def {name} : Interval :=\n  Interval.mk (({lo}) : ℚ) (({hi}) : ℚ) (by norm_num)"
    text = text[:start] + replacement + text[end:]

target.write_text(text)
print(f"wrote {target}")
