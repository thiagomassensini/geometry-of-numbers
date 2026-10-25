#!/usr/bin/env python3
"""Rebuild only the three unchanged source-synthesis modules actually imported."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
repo = root.parents[1]
base = "c4bcc38389c592681cde11a2b379079d6abd0cc9"
records = {}
for module in ["SchurBound", "NativeSynthesis", "Quadratures"]:
    p = root.parent / "native-vertical-synthesis" / f"{module}.lean"
    rel = str(p.relative_to(repo))
    original = subprocess.check_output(["git", "show", base + ":" + rel], cwd=repo)
    assert p.read_bytes() == original, rel
    subprocess.run(["bash", "compile_module.sh", module, str(p)], cwd=root, check=True)
    records[module] = {"source": rel, "source_sha256": hashlib.sha256(original).hexdigest(),
                      "olean_sha256": hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest()}
(root / "evidence").mkdir(exist_ok=True)
(root / "evidence/upstream.json").write_text(json.dumps({"base": base, "modules": records}, indent=2) + "\n")
print("PASS: unchanged PR92 source synthesis rebuilt from its exact base.")
