# Validation ledger — radius-51 contour route

## C0 isolation and source audit

- `git fetch origin` completed before creating the new branch.
- PR #304: open/mergeable, base `main`, head `agent/c2-central-hankel2-allorder-20261107` at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- PR #311: open/mergeable, based on the B1 branch, head `agent/c2-central-ten-heights-b2-20261108` at `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`.
- PR #306: open/mergeable, base `main`, head `agent/c2-central-contour51-20261108` at `e96e3a132ee6c4f494fee97e3ff1753f606514fc`. Its two original files were read in full and copied byte-for-byte; the original PR branch was not checked out for writing or modified.
- Rechecked after the C3 checkpoint through GitHub on 2026-11-08: #304 and #311 remain open/mergeable; #306 remains open/mergeable and draft. Their heads are unchanged at the SHAs above. The new branch is based directly on B2 at `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`.
- At this pre-C2-closure checkpoint, draft PR #314 was stacked on B2 base `agent/c2-central-ten-heights-b2-20261108` at `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`, through head `5885790ece27bcc85076f53bf2cca24c44e21057`. The final C2 closure and PR refresh are recorded below.
- New base commit: `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- Lean toolchain: `leanprover/lean4:v4.32.0`; local `lean --version` reports Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Read-only imported build paths: C2 integration and external artifacts under `/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/`; B2 output `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`; B1 rational-gate output `/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`; Mathlib output `/home/thlinux/geometry-of-numbers/.lake/build/lib/lean`.
- The primary checkout was already dirty with unrelated untracked `GeometryOfNumbers/Analysis/IntegerMomentGramPositivity.lean` and `research/entrywise-moment-square/`; neither is in this worktree or included in this branch.
- No upstream C2 integration or C3 module was rebuilt. The C3 Arb script was executed in this worktree and its own evidence files. C5 and other Luna worktrees/caches were not used as build outputs.

## Investigation source identity

- Copied `RESEARCH.md` blob SHA-1: `be54ffdc43332c962aba914e18cc3fa07b4a9c4e`; the local copied file has the same Git blob SHA.
- Copied `reproduce.py` blob SHA-1: `b286f6b9c01d55e94dac4235f174b914163ce093`; the local copied file has the same Git blob SHA.
- Reproduction command: `python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py`.
- Reproduction output: `evidence/PR306-reproduce.log`; SHA-256 `574b43aa21bf2e0f8b3c72c64da6c1ca888069cd85088916107db6140f803bfd`.
- The rerun produced the recorded sample maximum `0.634520221651175412`, sample mean `0.569580198724316508`, and positive floating-point residual probes `e_0,…,e_5`. This is only a consistency check of the experiment; it does not certify any continuum bound or sign.

## C3 Arb interval certificate

- Certificate: `C3_ARb_CERTIFICATE.md`; implementation: `certify_contour51_bound.py`; per-arc interval enclosures: `evidence/C3_ARb_ARCS.csv`.
- Command: `python research/native-moving-schur-sigma/mission-central-contour51-20261108/certify_contour51_bound.py --csv research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/C3_ARb_ARCS.csv`.
- Environment: Python 3.12.12, python-flint 0.8.0, 160-bit Arb precision, 512 rational arcs, Taylor degree 32.
- Result: maximum certified `|xi'/xi| < 1.492825`, hence maximum `|R| < 0.746413 < 4/5`; minimum certified `|zeta|` lower bound `>0.942660`. The script checked the Taylor-domain pole exclusion and every arc inequality.
- Proof boundary: this is a rigorous computer-assisted Arb certificate, not a Lean theorem. The C4 Lean theorem still takes the circle bound/identity as explicit hypotheses.
- SHA-256: script `c24787628f719a605a12a3e1b00558864d8e4b00dbfc0632c1914096a5fd6478`; certificate note `a606656428f710fdcc7ea2ac959fe0d358c20aaf9069945ee558154ba2eb0307`; arc CSV `c1a2a37fcd1450c34181edd0f6fe7fac334fdf750be153d708c15f2e0fb90519`; run log `8e76addb77abdacf677b4e0a019b2e52bb86359f4172e1d4c8291b4eba868609`.

## Required provenance sources inspected

- `SigmaNativeContinuation.lean`: `completedNativeCharacteristicContinuation` is the existing regularized-completed-zeta expression in `operatorHeightParameter`; its analyticity, evenness, and equality to the native characteristic on the native strip are explicit.
- `SigmaHeight50Integration.lean` and B2's `SigmaCentralTenHeightRootBridge.lean`: the same ten heights and positive/negative root statements come from B2; the moments are not rebuilt from zeros.
- `RHHeight.Main`: `rh_up_to_height_fiftytwo`, `low_height`, and `ncount_three_fiftytwo` are imported from the existing compiled certificate. `RHHeight.Skeleton.mem_and_simple_of_Ncount_le` converts the multiplicity-weighted count into exact membership and simplicity once ten distinct roots are supplied.
- C1 uses `Ncount` with multiplicity, not B2's distinct-point count alone.

## C1 radius-51 root classification

- Module: `SigmaContour51DiskBridge.lean`; exact original continuation is `completedNativeCharacteristicContinuation`.
- Command: `CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51DiskBridge`, redirecting output to `evidence/C1_SigmaContour51DiskBridge-build.log`.
- Result: exit 0 under Lean 4.32.0 with `-DwarningAsError=true`. Before compiling, `ps -C lean` and `ps -C lake` returned no processes; `/proc/meminfo` reported 60.8 GiB available. Only the exclusive output root was written; imported C2/C3, B2, B1, and Mathlib outputs remained read-only.
- The module proves `sigmaHeight52_count_exhausts_ten_zeros_with_multiplicity` and `sigmaContour51_original_characteristic_roots`. Each `#print axioms` result is `[propext, Classical.choice, Quot.sound]`; neither uses `sorryAx` or a new axiom.
- SHA-256: source `e2e14ecdb3e01cc5de70c96f3c8f00f0c706a25daa3649ed7ffe0f9cceb69b9f`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51DiskBridge.olean` `1708d91c5541f0a0877e10f0a6f9936284210c04a6805b1b83e957cad786f33c`; successful log `6e958af821b714ad83e4180a5d01b1b685c9c918331172f551dfc8a7417e747d`.
- Failed first attempt is preserved as `evidence/C1_SigmaContour51DiskBridge-attempt1-failed.log`, SHA-256 `e315197b11f3dc015fa7a6a18461be9e2ec9d17ff78d7b7603d926cb9d4f3413`. It records an earlier uncompilable draft and its recovery axiom printouts; only the successful log above corresponds to the published source.
- Publication: commit `4b104771b7cc3dfbd487584b57b5bba1680e273e` is pushed to `agent/c2-contour51-20261108` and included in draft PR #314, which remains unmerged.
- At this C1-only checkpoint, C2's finite contour-residue identity and the C3-to-Lean analytic estimate were separate open obligations; the later C2 section below closes the first. C1 alone does not establish positivity.

## C2 local residue and Cauchy helpers — historical intermediate commits

- Module: `SigmaContour51Residue.lean`; exact command is recorded in `evidence/BUILD_COMMANDS.md` and the successful output is `evidence/C2_SigmaContour51Residue-build.log`.
- Result: exit 0 under Lean 4.32.0 with `-DwarningAsError=true`. The build ran in the exclusive output root `/home/thlinux/tmp/c2-contour51-20261108-lean432`. The user explicitly authorized parallel execution while C5 PID `151152` continued in a separate worktree/cache; available memory was about 56.6 GiB. No C5 path was read or written.
- The compiled declarations are `analytic_simple_zero_log_derivative_residue`, `analytic_simple_zero_log_derivative_pole_cancellation`, `sigmaContour51_original_characteristic_logDerivative_residue`, and `normalized_circle_integral_coefficient`. Each `#print axioms` result is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom.
- SHA-256: source `b42c2eca6e5790bbe3b03c1ade1f7b2dffd2b2c318badf0fd6395a27c333abd9`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51Residue.olean` `19e1be7565602d94ecd355f87ad27bc11d4f0b0071cb8c7dc268eb04f44f77a1`; successful log `fcb85459a3f4d8dbb0b458ca1f2f2c7324d2c3d6166bbe6f37108ed40d815e1f`.
- Failed diagnostic attempts are preserved separately: attempt 1 `a49804507ec5971d83ad53c7530273479405ac1bb2c89a8bdc52ecbeac617257`, attempt 2 `58baf85c1b431c4594053b8d07ff2463617365523ea41c8996a0a33565eb07ec`, attempt 3 `6ff3ffa3e2fadc1d195fbe9325eed13928ba88386e7bff03027946f938586e61`. Trailing whitespace from Lean's formatted diagnostics was removed from attempts 1 and 2; theorem and error text is otherwise unchanged. Their `sorryAx` reports are Lean recovery output for failed declarations, not the successful module.
- Publication: commit `4a8f4cb6f73a8d92b739297223dd535209f2a07f` is pushed to `agent/c2-contour51-20261108`; draft PR #314 remains open and unmerged.
- Historical proof boundary at commit `4a8f4cb`: these were local residue/removal and Cauchy helpers. The later final C2 build below supersedes the statement that global gluing remained open.

## C2 finite-pole circle-kernel helper — historical intermediate commit

- Module: `SigmaContour51FiniteContour.lean`; exact command is recorded in `evidence/BUILD_COMMANDS.md`, and the successful output is `evidence/C2_SigmaContour51FiniteContour-build.log`.
- Result: exit 0 under Lean 4.32.0 with `-DwarningAsError=true`, using the exclusive output root `/home/thlinux/tmp/c2-contour51-20261108-lean432`. `contour51_pole_kernel_integrable_and_integral_zero` proves integrability and zero circle integral of `(z-a)⁻¹ * z^(-(n+1))` for every `n : ℕ`, assuming `a ∈ ball 0 51` and `a ≠ 0`. `contour51_cauchy_reduction_of_finite_correction` assembles the finite correction and Cauchy formula, assuming `G` is `DiffContOnCl` on the disk and `hcorr` holds on its boundary. Both `#print axioms` results are `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom.
- The build ran while C5 PID `151152` was active in its separate worktree/cache, under the user's explicit parallel-build authorization; about 55 GiB was available. This worktree did not access C5 files or cache.
- SHA-256: source `7c07b71dad3cb582d7d0e03294fc116ea6fc4dc5f66e1d1d7bf0d8a8004f5832`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51FiniteContour.olean` `ed5a4fe05febee0e7a54f677920b72396d023d1980385abb2d80ce8442c453e5`; successful log `dc0767f8039243da8fc07213112050484115dbe8fe352779d12745460a86de67`.
- Eight initial failed diagnostic attempts are preserved as `evidence/C2_SigmaContour51FiniteContour-attempt1-failed.log` through `attempt8-failed.log`; attempt 11 is preserved as `attempt11-failed.log`. Lean's trailing whitespace was removed from diagnostic copies. SHA-256 in order for attempts 1–8: `ef83179259200a41bd4475d2006cf5a5753082f915a42b953446da921bd5a6a9`, `7022d3d2fd583bb589c791f1945ec2915ef8896803ac272ad8560b270904c707`, `c59269ae88d80aabe125401118b017f88391f5d89c40de82f762f605c6d009a8`, `e979e623fae96b9d029e5b9599ce5bb6958244dd5ad6057774f55f48e205fa75`, `fe46fb7616b49e730768981a715fd31149a2ca7db93cd432c1c8654c5df05b0d`, `5c2e33fa71581ee07254dffc31af1c0a10cc88972c3fbad257fdc013ed6f4e8f`, `eb4b8a1cd9fdffde6d40454d40ec1355835fe424243ab909de627e8e10f8c54e`, `6c387b5f83c3e314243bf7ec1fded8dedddbce07e3341a9b7f712d12e30a6a4c`; attempt 11: `449cefa0bd35fabc19bb7f8c18a76136319cbfc33febdc2549343662ae17e17e`.
- Historical proof boundary at commit `5885790`: the finite sum and Cauchy step were conditional on a corrected function and boundary relation. The later final C2 build below constructs the correction and identifies the original coefficient.

## C2 global source-normalized contour identity — complete

- Modules: `SigmaContour51Residue.lean` and `SigmaContour51FiniteContour.lean`. After updating the helper's documentation to record the completed gluing theorem, both modules were rebuilt sequentially. The fixed-root theorem `exists_completedNative_contour51_corrected_log_derivative` selects one C1 list `ts : Fin 10 → ℝ`, exposes the exact B2 height box for each index, and proves finite analytic gluing for every kernel order. `completedNative_contour51_jet_residue_identity` uses this same `ts` for every `n` and proves

  `normalized ∮ R(z)/z^(2*n+2) = completedSigmaLogJet 0 n - ∑ i : Fin 10, (ts i)^(-2*n-2)`.

  The correction is analytic on the closed radius-51 disk, each pole kernel has zero circle integral, the corrected Taylor coefficient is computed from the original response, and the Carry bridge identifies it with the original central jet. No zero-defined source, Hadamard factorization, new axiom, `sorry`, or `admit` is used.
- Build: Lean 4.32.0, `-DwarningAsError=true`, exit 0, with C5 PID `151152` active only in its isolated worktree/cache and about 51 GiB available. The exclusive C2 output root was `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- Exact command: the common environment in `evidence/BUILD_COMMANDS.md`, first module `SigmaContour51Residue` with log `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51Residue-attempt5.log`, then `SigmaContour51FiniteContour` with log `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51FiniteContour-attempt34.log`.
- Axiom audit: the pole-kernel integral, conditional Cauchy assembly, generic finite gluing, completed-native specialization, and source-normalized all-order identity each report `[propext, Classical.choice, Quot.sound]`.
- SHA-256: residue source `ad83a9810d9c0cd7b3f1611a69efa58dddb401a954c0b22ab4c2fa81001dcb76`, OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51Residue.olean` `8fecbe901c8eeb6cb50064a2867e1c61e11adfe839983668ae84b104abeea645`, success log `C2_SigmaContour51Residue-attempt5-success.log` `fcb85459a3f4d8dbb0b458ca1f2f2c7324d2c3d6166bbe6f37108ed40d815e1f`; finite-contour source `56fa6e0cb963c83beeb9aae4dc4dc57c3f18436d2607fb3a3cba25f085077597`, OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51FiniteContour.olean` `f1e69205fee1c8d6c447235e70b81803a52f9bc96b22c4e8ff784e04aeaa32d6`, success log `C2_SigmaContour51FiniteContour-attempt34-success.log` `aa1b00690c688f0a5130953f1e254590dfe705d98667714d0611c2faef91f07b`.
- Proof status: C2 is closed for one fixed ten-height list and every `n`. The Arb certificate is still not a Lean theorem, and no rational lower margins for the six central residual signs `e_0,…,e_5` have been certified. See the remaining-obligations section below and `RESTART_HERE.md`.

## C2→C4→C6 composition for the original source — conditional theorem complete

- Module: `SigmaContour51SourceTail.lean`. `contour51_scales_in_rational_boxes` turns C2's exposed B2 height intervals into the exact reciprocal-square scale boxes used by C6. `completedNativeContour51_decomposition` defines the ten-mode residual from the original `completedSigmaLogJet`. `completedNative_sigmaPadeD_pos_of_contour51_bound` uses the fixed all-order C2 identity, C4's radius conversion, and C6's exact rational gates to conclude the original `sigmaPadeD` positivity for every `s`, conditional only on the full-circle bound `‖R‖≤4/5` and the six signs `e_0,…,e_5≥0`. The added `completedNative_sigmaPadeD_zero_pos_of_contour51_bound` isolates the first determinant and needs only `e_0≥0` and `e_2≥0`; the C4 bound on `|e_1|` proves the middle moment stays positive.
- Build: Lean 4.32.0 with `-DwarningAsError=true`, exit 0, in the exclusive C2 output root; C5 PID `151152` remained isolated in its own worktree/cache and about 51 GiB remained available.
- Exact command: common environment in `evidence/BUILD_COMMANDS.md`, module `SigmaContour51SourceTail`, final log `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51SourceTail-attempt10.log`.
- Axiom audit: all five printed declarations report `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom.
- SHA-256: source `5991dbd9b867131f6f64dfc6c50383a1980afea399301f7cd6526f4d6eb9bcc4`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51SourceTail.olean` `4e20760782891093b979c388f720d00ba4f243ae53baf1dc519c97a01991a2d2`; evidence log `C2_SigmaContour51SourceTail-attempt10-success.log` `b0fc568ebe40b00f7acf189942aee2e695f5e7052ac6b07e9c3cb0739ad2d817`.
- Boundary: this is conditional. Arb certifies the circle estimate externally but it is not yet a Lean premise derived in the module, and there are no rational lower bounds for the six central residual signs. No unconditional `∀ s, 0 < sigmaPadeD 0 s` theorem is claimed.

## C4/C6 conditional tail and gates

- Module: `SigmaContour51RationalGate.lean`; command is in `evidence/BUILD_COMMANDS.md`, successful log is `evidence/C4C6_SigmaContour51RationalGate-build.log`.
- Result: exit 0 under Lean 4.32.0 with `-DwarningAsError=true`. The build used the exclusive output root `/home/thlinux/tmp/c2-contour51-20261108-lean432`. C5 PID `151152` remained active in its separate worktree/cache under the user's explicit parallel-build authorization; about 56.6 GiB was available. No C5 worktree/cache was accessed.
- `#print axioms` for `contour40EarlyMargin_pos`, `contour40_radius_conversion`, `contour40_tail_of_circle_identity`, and `sigmaPadeD_pos_of_contour40_tail` reports `[propext, Classical.choice, Quot.sound]` for each, with no `sorryAx` or new axiom.
- The module proves the normalized circle-integral bound, exact radius conversion, all four shallow margins, B1's large-window implication, and positivity of the original `sigmaPadeD` conditional on `hdecomp`, `hbox`, the global `C=40` tail, and six finite signs. The tail theorem itself assumes a C2 contour identity and the circle bound `‖R‖ ≤ 4/5`. None of these hypotheses is silently discharged.
- SHA-256: source `3f274709c444c13b8d97f365be9e785e36c9cd64a957b68477038ef0965f488e`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51RationalGate.olean` `81f71953d3f154de54a9539c1a089cea4a59a657bf84af1812b535caf01bbdd2`; successful log `255524b0b4a51c05a1dee952e333c70a8abad9eef2f818660ee8c17c6362c52e`.
- Failed diagnostic attempts: attempt 1 `b943a80e6a10230495397ce1a9510d59fc452e696454bd0d6021adf33f2a8d4d`; attempt 2 `efb5ae0d8559f8a234412fada26aec1c62ae482ef19fda711828b3b354368449`. Their `sorryAx` output is Lean recovery from failed declarations; the successful attempt 3 is authoritative.

## Remaining analytic and finite inputs

- C3's bound `‖R z‖ ≤ 4/5` on the radius-51 circle has a rigorous Arb/Acb certificate, with maximum `<0.746413`, but it is not yet a Lean theorem. C4's `C=40` tail remains conditional on that bound.
- There are no rational lower enclosures for the central residual signs `e_0,…,e_5` in this branch. The mpmath values in `evidence/PR306-reproduce.log` are probes only. Under the C3 premise, the exact C4 upper bounds are `|e_n| ≤ 40/2500^(n+1)`; these do not supply signs.
- C6's four shallow determinant gates have exact-rational positivity proofs; their decimal displays are approximately `1.233805751396619e-10`, `2.370461448625535e-15`, `1.677704301041960e-20`, and `4.956177598481227e-26` for `s=0,1,2,3`. These are determinant margins under the explicit tail/sign/source-box premises, not margins for `e_n`.
- The C5 branch's conditional displaced determinant results at `d=99/2000` and `d=1/10` do not certify central `e_n` signs. Reusable components are general rational interval arithmetic, node-evaluation lemmas, and original-source normalization/transport; reuse requires a proved specialization at `d=0`. Do not duplicate its Bernoulli table or zeta/Gamma node certification.
- Smallest first-window advance: prove the circle bound in Lean and derive source bounds `e_0 ≥ 0` and `e_2 ≥ 0`; C4 then bounds `|e_1|` and a focused `s=0` determinant gate can prove `sigmaPadeD 0 0 > 0`. For the existing all-order wrapper, the six signs `e_0,…,e_5 ≥ 0` remain explicit.
- Therefore this branch does not claim unconditional central positivity. Keep the remaining analytic and sign assumptions visible in all subsequent theorems.
