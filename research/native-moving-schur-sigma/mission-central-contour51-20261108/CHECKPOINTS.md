# C2 finite contour at radius 51 — checkpoints

- [x] **C0 — isolate and audit the investigation.** Branch `agent/c2-contour51-20261108` starts at B2 PR #311 HEAD `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`. PR #306's original branch remains untouched; its `RESEARCH.md` and `reproduce.py` are copied byte-for-byte. The numerical probe was rerun and its output is explicitly non-certified. Lean 4.32 and an exclusive output root are recorded in `VALIDATION.md`.
- [ ] **C1 — exact roots in the closed disk `|z| ≤ 51`.** Use B2's ten ordered height witnesses, the height-52 RH and multiplicity count `RHHeight.ncount_three_fiftytwo`, and `RHHeight.mem_and_simple_of_Ncount_le`. Prove all roots are exactly the twenty signed heights, all are simple, and the radius-51 circle is zero-free.
- [ ] **C2 — finite residue identity.** Prove the all-`n` residual contour formula for the original characteristic's jets, or document an explicit analytic reduction and the missing infrastructure.
- [ ] **C3 — uniform radius-51 logarithmic-derivative bound.** Validate the proposed inequality on the whole circle with rigorous bounds, or produce a certified counterexample and revise the route.
- [ ] **C4 — all-order residual tail.** Derive the `40*(1/2500)^(n+1)` bound from C2/C3.
- [ ] **C5 — six finite residual signs.** Certify `e_n ≥ 0` directly from the original characteristic for `0 ≤ n ≤ 5`.
- [ ] **C6 — exact finite gates and conditional closure.** Prove the four rational margins in Lean, reuse B1 for `s ≥ 4`, and keep the final positivity theorem conditional unless C3 and C5 are closed.
