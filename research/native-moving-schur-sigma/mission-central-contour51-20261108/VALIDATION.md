# Validation ledger — radius-51 contour route

## C3 generic complex interval division

- **Módulo:** `SigmaContour51ComplexIntervalDivision.lean`.
- **Teoremas compilados:** `Interval.contains_squareRange`,
  `Interval.contains_reciprocalPositive`, `ComplexInterval.contains_normSqRange` e
  `ComplexInterval.contains_divBox`.
- **Hipóteses:** `contains_divBox` precisa de caixas contendo numerador `z` e denominador `w`, uma
  caixa `denNormSq` com `Complex.normSq w` e `0 < denNormSq.lo`. `normSqRange` constrói uma caixa
  candidata para a norma quadrada; provar que seu extremo inferior é positivo depende da caixa
  concreta do chamador. Este módulo não inclui valores de zeta, digamma, fonte ou saídas Arb.
- **Build:** Lean 4.32.0, `-DwarningAsError=true`, código de saída 0, output exclusivo
  `/home/thlinux/tmp/c2-contour51-20261108-lean432`. O comando integral está em
  `evidence/BUILD_COMMANDS.md`; a saída compilada está em
  `evidence/C3_SigmaContour51ComplexIntervalDivision-success.log`.
- **Auditoria:** os quatro teoremas reportam somente `[propext, Classical.choice, Quot.sound]`.
  A fonte não contém `sorry`, `admit`, `native_decide` ou declaração de axioma.
- **Tentativas:** os quatro primeiros diagnósticos encontraram erros de orientação dos lemas de
  quadrado/recíproco, escopo das hipóteses de positividade e reescrita das fórmulas de divisão; o
  quinto compilou. Os erros foram corrigidos no fonte final; os diagnósticos recuperáveis ficaram
  no output transitório, não em arquivo bruto de evidência.
- **SHA-256:** fonte `d10933c086f71ddfe48ad9b6fdd1ef5f3bf4ae95fe5cd6a072cb914195a4d0c9`; OLean
  `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ComplexIntervalDivision.olean`
  `ef60f81a875eeeeedf546f6c1da524411b808794a2766f98cdf266ca782b9684`; log
  `5b13ba5040f413bc1cfd8c6c2f63fe266e0c994e7f5184d00d3d1cccf2850eef`.

## C3 composição intervalar da resposta original

- **Módulo e resultados:** `SigmaContour51ArbIntervalComposition.lean` prova
  `contour51ArbSigmaXiLogDerivativeBox_contains`,
  `contour51ArbOriginalResponseBox_contains_lower_path`,
  `contour51ArbN0ResidualIntegrandBox_contains` e o lema genérico
  `contour51ArbResidualIntegrandBox_contains` para todo `n`. Para as caixas dos componentes,
  `contour51Arb4096N0ArcEvaluatorInclusion_of_component_boxes` e
  `contour51Arb4096N0AllArcEvaluatorInclusion_of_component_boxes` derivam a inclusão da parte real
  de ordem zero em cada arco, sob comparação racional com os extremos Arb.
- **Hipóteses explícitas:** caixas uniformes no arco para `s`, `ζ(s)`, `ζ′(s)`, `digamma(s/2)`,
  `log π` e o parâmetro; caixas de norma quadrada com limite inferior positivo para os divisores;
  e, no adaptador n=0, comparações da caixa composta com os extremos externos. O módulo não fornece
  esses dados. O adaptador por extremos de n=1 e n=2 não existe ainda; assim
  `contour51Arb4096FirstThreeArcEvaluatorInclusion` e a margem determinantal `1/10^9` continuam
  abertas/condicionais. As seis ordens e a ponte dos 512 arcos para `hR` também permanecem abertas.
- **Build/auditoria:** Lean 4.32.0, `-DwarningAsError=true`, output exclusivo C2. Os sete teoremas
  auditados reportam somente `[propext, Classical.choice, Quot.sound]`; não há `sorry`, `admit`,
  `native_decide` ou axiomas declarados.
- **Evidência:** comando, hipótese de cada caixa, limitações e hashes estão em
  `evidence/C3_SigmaContour51ArbIntervalComposition.md`; log em
  `evidence/C3_SigmaContour51ArbIntervalComposition-success.log`. Tentativas 1–4 falhas e a
  compilação intermediária da tentativa 5 estão preservadas na mesma pasta, com hashes e causas na
  nota; a tentativa 6 corresponde ao log final. As mensagens `sorryAx` em logs 1–2 são apenas
  recuperação de declarações que não elaboraram, não dependências do fonte final, cuja auditoria
  contém somente axiomas padrão.

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
- Proof status: C2 is closed for one fixed ten-height list and every `n`. The Arb certificate now gives exact rational lower and upper interval endpoints for the six central residuals; the interval transfer remains an explicit Lean hypothesis, not a theorem.
- Publication: commit `1a4920b07d542e0f8077ef516d8c36981b1759f8` is pushed to `agent/c2-contour51-20261108`. Draft PR #314's description was refreshed; GitHub reports it open, draft, unmerged, based on B2 PR #311, and `CLEAN`.

## C2→C4→C6 composition for the original source — conditional theorem complete

- Module: `SigmaContour51SourceTail.lean`. `contour51_scales_in_rational_boxes` turns C2's exposed B2 height intervals into the exact reciprocal-square scale boxes used by C6. `completedNativeContour51_decomposition` defines the ten-mode residual from the original `completedSigmaLogJet`. `completedNative_sigmaPadeD_pos_of_contour51_bound` uses the fixed all-order C2 identity, C4's radius conversion, and C6's exact rational gates to conclude the original `sigmaPadeD` positivity for every `s`, conditional only on the full-circle bound `‖R‖≤4/5` and the six signs `e_0,…,e_5≥0`. The added `completedNative_sigmaPadeD_zero_pos_of_contour51_bound` isolates the first determinant and needs only `e_0≥0` and `e_2≥0`; the C4 bound on `|e_1|` proves the middle moment stays positive.
- Build: Lean 4.32.0 with `-DwarningAsError=true`, exit 0, in the exclusive C2 output root; C5 PID `151152` remained isolated in its own worktree/cache and about 51 GiB remained available.
- Exact command: common environment in `evidence/BUILD_COMMANDS.md`, module `SigmaContour51SourceTail`, final log `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51SourceTail-attempt10.log`.
- Axiom audit: all five printed declarations report `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom.
- SHA-256: source `5991dbd9b867131f6f64dfc6c50383a1980afea399301f7cd6526f4d6eb9bcc4`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51SourceTail.olean` `4e20760782891093b979c388f720d00ba4f243ae53baf1dc519c97a01991a2d2`; evidence log `C2_SigmaContour51SourceTail-attempt10-success.log` `b0fc568ebe40b00f7acf189942aee2e695f5e7052ac6b07e9c3cb0739ad2d817`.
- Boundary: this is conditional. Arb certifies the circle estimate and residual intervals externally, but neither has yet been transferred to the Lean contour integrals. No unconditional `∀ s, 0 < sigmaPadeD 0 s` theorem is claimed.

## C4/C6 conditional tail and gates

- Module: `SigmaContour51RationalGate.lean`; command is in `evidence/BUILD_COMMANDS.md`, successful log is `evidence/C4C6_SigmaContour51RationalGate-build.log`.
- Result: exit 0 under Lean 4.32.0 with `-DwarningAsError=true`. The build used the exclusive output root `/home/thlinux/tmp/c2-contour51-20261108-lean432`. C5 PID `151152` remained active in its separate worktree/cache under the user's explicit parallel-build authorization; about 56.6 GiB was available. No C5 worktree/cache was accessed.
- `#print axioms` for `contour40EarlyMargin_pos`, `contour40_radius_conversion`, `contour40_tail_of_circle_identity`, and `sigmaPadeD_pos_of_contour40_tail` reports `[propext, Classical.choice, Quot.sound]` for each, with no `sorryAx` or new axiom.
- The module proves the normalized circle-integral bound, exact radius conversion, all four shallow margins, B1's large-window implication, and positivity of the original `sigmaPadeD` conditional on `hdecomp`, `hbox`, the global `C=40` tail, and six finite signs. The tail theorem itself assumes a C2 contour identity and the circle bound `‖R‖ ≤ 4/5`. None of these hypotheses is silently discharged.
- SHA-256: source `3f274709c444c13b8d97f365be9e785e36c9cd64a957b68477038ef0965f488e`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51RationalGate.olean` `81f71953d3f154de54a9539c1a089cea4a59a657bf84af1812b535caf01bbdd2`; successful log `255524b0b4a51c05a1dee952e333c70a8abad9eef2f818660ee8c17c6362c52e`.
- Failed diagnostic attempts: attempt 1 `b943a80e6a10230495397ce1a9510d59fc452e696454bd0d6021adf33f2a8d4d`; attempt 2 `efb5ae0d8559f8a234412fada26aec1c62ae482ef19fda711828b3b354368449`. Their `sorryAx` output is Lean recovery from failed declarations; the successful attempt 3 is authoritative.

## Remaining analytic and finite inputs

- C3's bound `‖R z‖ ≤ 4/5` on the radius-51 circle has a rigorous Arb/Acb certificate, with maximum `<0.746413`, but it is not yet a Lean theorem. C4's `C=40` tail remains conditional on that bound.
- The 4096-arc Arb run now supplies exact rational enclosures and strict positive rational lower margins for all six central residuals; see the new section below. The older mpmath values in `evidence/PR306-reproduce.log` are probes only. Under the separate C3 Lean premise, the exact C4 upper bounds are `|e_n| ≤ 40/2500^(n+1)`; these are not the source of the Arb lower signs.
- C6's four shallow determinant gates have exact-rational positivity proofs; their decimal displays are approximately `1.233805751396619e-10`, `2.370461448625535e-15`, `1.677704301041960e-20`, and `4.956177598481227e-26` for `s=0,1,2,3`. These are determinant margins under the explicit tail/sign/source-box premises, not margins for `e_n`.
- The C5 branch's conditional displaced determinant results at `d=99/2000` and `d=1/10` do not certify central `e_n` signs. Reusable components are general rational interval arithmetic, node-evaluation lemmas, and original-source normalization/transport; reuse requires a proved specialization at `d=0`. Do not duplicate its Bernoulli table or zeta/Gamma node certification.
- Smallest first-window advance: prove `contour51ArbFirstThreeResidualIntervalBounds` from the Arb enclosures at `n=0,1,2`. The new direct first-window theorem then proves `1/1000000000 < sigmaPadeD 0 0` without a circle-bound premise. The all-window wrapper still needs the Lean circle bound and all six interval transfers.
- Therefore this branch does not claim unconditional central positivity. Keep the remaining analytic and sign assumptions visible in all subsequent theorems.

## Exact ten-mode width budgets and C5 center specialization

- New module: `research/native-moving-schur-sigma/SigmaContour51BoxSensitivity.lean`. It defines the B2 ten-mode box width `highMoment n - lowMoment n` and proves in Lean 4.32 that, for `n≤5`, it is strictly below the rational budgets `14/10^6`, `9/10^8`, `6/10^10`, `4/10^12`, `3/10^14`, and `2/10^16`. The theorem `completedNativeContour51Residual_nonneg_of_jet_margin` gives a sufficient original-jet route to signs, but no original-jet lower enclosure is supplied. Independently, the contour Arb intervals give external margins; only their Lean transfer remains open.
- C5 center transport is explicit in five compiled theorems: `c5CentralDisplacedProduct_eq_characteristic_square`, `c5CentralDisplacedProduct_eq_continuation_square`, `c5CentralSource_log_derivative_eq_twice_original_jets`, `c5CentralSource_log_derivative_coeff_eq_twice_original_jet`, and `c5CentralResidual_eq_half_source_moment_sub_modes`. At `d=0`, the C5 product is exactly the square of `completedNativeOperatorCharacteristic`; under the explicit genuine-strip hypothesis, it equals the square of `completedNativeCharacteristicContinuation` used by the contour argument. The generic source recurrence gives coefficient `2*completedSigmaLogJet 0 n`; and `e_n` is half the C5 source moment minus the ten-mode power sum. Each declaration prints only `[propext, Classical.choice, Quot.sound]`. The existing `SigmaSourceBezoutAudit.lean` also compiles and reports 57,386 type/body dependencies with standard axioms only, retaining `completedSigmaDensity`, `displacedProductC`, `completedSigmaLogJet`, and the original sigma matrix.
- No C5 interval boxes were moved from `d=99/2000` or `d=1/10` to `d=0`. Doing so still requires a quantitative displacement estimate or a new central evaluation. The general rational ball arithmetic, fixed-node evaluators, and original-source normalization/transport remain shareable. No Bernoulli table or zeta/Gamma node certificate was rebuilt here.
- The exact-rational sensitivity script `analyze_box_width_sensitivity.py` reports widths approximately `1.3038935355470468e-5`, `8.8707651982351861e-8`, `5.8021702152449330e-10`, `3.6785120434605851e-12`, `2.2551276469308842e-14`, and `1.3430971414644236e-16`; its comparison to mpmath probes is explicitly diagnostic, not a sign proof. The per-index output is `evidence/C2_box_sensitivity.log`.
- Build environment: Lean 4.32.0, `-DwarningAsError=true`, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`; no C5 cache was used as output. The C5 prefix-224 process PID `151152` remained isolated in its own worktree while these sequential C2 builds ran, with over 53 GiB available.
- Final module source SHA-256 `07afd32690e14ab322f96b8213630339ae98da2c37a91b72441247f4626d8326`; OLean `e10545e1d383979701a23b6c49e51a360eaf693cb6523e79addccf2aeca6aaed`; final success log `evidence/C2_SigmaContour51BoxSensitivity-attempt12-success.log` SHA-256 `df26f232dfdd46e3161c9e6b263352b5b8ac09c6db2a3cf87f2353ee3e09e662`.
- Source recurrence source SHA-256 `5b9e8d064dd4cb046479dc35dae0bde5613f37025111eff880c1922287b54378`; OLean `aeb6184f4deebc378eb9cf4329def2ab484cdfb2ed6937ffb903f42056e8d53d`. Its dependency/provenance audit source SHA-256 `6768ba437a008203adcd491c7d41cbed350c7ae73ce4e58fea6fdde7aabe6952`; OLean `aaf50f96c5a398cc0d15d11f27b85607983a660bb83243f1e1ae89f6766f2ac1`; successful audit log `evidence/C5_source_transport_audit.log` SHA-256 `62994a5533aef97b3754e0d8ffb0ca33e7f245a8fb16e6e52032862b4775b3cc`.
- Failed/intermediate attempts are retained as `C2_SigmaContour51BoxSensitivity-attempt1-failed.log` through `attempt7-failed.log`, `attempt8-success-intermediate.log`, `attempt10-failed.log`, and `attempt11-success.log`; the final proof with the continuation bridge's axiom audit is attempt 12. `C5_SourceBezout-missing-dependency.log` records the initial missing `SourceBezout.olean`; the module was then compiled into the exclusive C2 output directory before the final adapter build.
- The C3 status is unchanged: Arb/Acb proves `|R|<0.746413<4/5` on the complete circle, but there is still no Lean theorem connecting that certificate to `hR := ∀ z, ‖z‖=51 → ‖R z‖≤4/5`. Exact external rational lower margins for all six `e_n` are now available. The all-window conditional inputs are `hR` plus Lean transfers of all six intervals; the direct `s=0` interval gate needs only transfers for `n=0,1,2`.

## Arb residual interval adapter — compiled, with transfer hypothesis open

- External certificate: `certify_contour51_residuals.py` evaluates 4096 full rational arcs at 160-bit Arb precision, reusing the C3 Taylor-degree-32 zeta/zeta-prime enclosure and explicit Cauchy remainders. The script encloses the real part of the original normalized full-circle Cauchy integral after the exact lower-half parameterization and `R(-z)=-R(z)` reduction. Its exact rational endpoints are in `evidence/C3_ARb_RESIDUALS_4096.json`; the reproducible run is `evidence/C3_ARb_RESIDUALS_4096.log`.
- Lean module: `SigmaContour51ArbResidualGate.lean`. It records the exact endpoints, proves the rational strict lower and upper simplifications, proves a strict rational lower margin for the first determinant, and provides conditional theorems for residual signs, `sigmaPadeD 0 0`, and all-window `sigmaPadeD` positivity. The all-window theorem takes `contour51ArbResidualIntervalBounds`; the first-window theorem's type takes only `contour51ArbFirstThreeResidualIntervalBounds`. Both are outstanding external-certificate-to-Lean premises. Therefore none of these conditional wrappers is an unconditional theorem.
- First-window exact margin: `contour51ArbZeroDetMargin_gt_rational` proves the endpoint lower-bound expression exceeds `1/1000000000`; under the three source interval transfers, `completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals` therefore proves `1/1000000000 < sigmaPadeD 0 0`. Its expression `(lowMoment 0 + L_0)*(lowMoment 2 + L_2) - (highMoment 1 + U_1)^2` bounds the complete determinant, retaining `P_0 e_2 + e_0 P_2 - 2P_1e_1 + e_0e_2 - e_1^2` through the full product and square. This direct gate does not assume the C3 circle norm bound.
- Rational margins `L_n` and upper bounds `U_n`: `(9/1000, 1/100)`, `(9/10000000, 1/1000000)`, `(9/50000000000, 1/4000000000)`, `(1/25000000000000, 1/10000000000000)`, `(1/100000000000000000, 1/50000000000000000)`, and `(1/500000000000000000000, 1/100000000000000000000)` for `n=0,…,5`. Decimal endpoint displays and exact endpoint fractions are in `C3_ARb_CERTIFICATE.md` and the JSON.
- Lean 4.32.0 build: `-DwarningAsError=true`, exit 0, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`, while the authorized C5 build remained isolated in PID `151152`; about 47 GiB were available. `#print axioms` on every new theorem reports only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `admit`, or new axioms. Final successful log: `evidence/C2_SigmaContour51ArbResidualGate-attempt10-success.log`; attempt 8 is an intermediate successful build with the three-interval interface before the determinant lower bound was exposed in the theorem conclusion.
- SHA-256: final Lean source `39db5dc0028d55c531fbe313fd1c5177ef3d9e512c3e50ff38a79f06c4098a64`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbResidualGate.olean` `ffc1897bfcf1a5979a0255b2f3b020b50e325b54092f6d7d529bc4a4f36cd317`; success log `b44310ff5f2704de851b969114d7b34c46e784ef250131d7a60ced805e5f88ee`; residual evaluator `dc53900ee9b2d387da7f86af3a1e8783ef961cd2049131c27145c91cb52f95a5`; exact JSON `f446b03f600c6eaf20e6ba18ce260e6c3711cf5624b192cef895646a0086aab6`; Arb run log `8f98f7f9f170e3a90c319a1b538cf9c5ec892948db9e1eafdd945b8a623ab4cd`.
- Exact remaining proofs: (1) prove the 512-arc Arb enclosures imply Lean's `hR`, including pointwise interval inclusion and validation of complete-arc Taylor/Cauchy bounds; (2) prove the 4096-arc pointwise Arb ranges enclose the Lean evaluator and that their exact rational weighted sums give the recorded endpoint bounds. The theorem `contour51_intervalIntegral_bounds_of_uniform_partition` now proves the intervening integration step. The evaluator identity, its lower-path domain conditions, circle parameterization/orientation, parity reduction, and exact lower-path identity are compiled. For the first `s=0` result, step (2) is needed only for `n=0,1,2`. No determinant sign or positivity premise is silently assumed.

## Arb lower-path identity — compiled, numerical inclusion still open

- Module: `SigmaContour51ArbContourBridge.lean`. It proves from the original continuation's evenness that `contour51OriginalResponse` is odd and `contour51OriginalResidualQuotient n` is even; the angular quotient is π-periodic. Using C1's exact zero-free radius-51 boundary classification, it proves continuity and integrability without adding a hypothesis.
- Exact theorem: `contour51OriginalResidualIntegral_eq_lower_path n` identifies the original normalized C2 contour integral with `∫ u in 0..1, Q_n(circleMap 0 51 (-π*u))`. The proof handles the positive full-circle orientation, the `i z` derivative factor, the half-circle symmetry, and the change of variable to the same lower path used by `certify_contour51_residuals.py`.
- Interval interface: `contour51ArbLowerPathResidualIntervalBounds` records the exact two-sided inclusions directly for the external Arb path integrals. `contour51ArbResidualIntervalBounds_of_lower_path_bounds` adapts all six to the existing C4/C6 gates; the first-three adapter handles only `n≤2`. `completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals` proves the first central determinant under those first-three inclusions, with `1/1000000000 < sigmaPadeD 0 0` and no `hR` premise.
- The new Lean propositions and theorem hypotheses are explicit: periodicity and path reduction are unconditional mathematical identities; all-six/all-three bounds remain open path-integral inclusion hypotheses. The old full-circle `contour51ArbResidualIntervalBounds` is no longer an independent obligation once the lower-path proposition is proved.
- Build: the common command in `evidence/BUILD_COMMANDS.md`, `MODULE_NAME=SigmaContour51ArbContourBridge`, Lean 4.32.0, `-DwarningAsError=true`, exit 0, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`. The final log is `C3_SigmaContour51ArbContourBridge-build.log`.
- Axiom audit: all printed new theorems report only `[propext, Classical.choice, Quot.sound]`. Search of the final module found no `sorry`, `admit`, or declared axiom.
- Still open for C3→Lean: the 512-arc certificate proves externally `|R|<0.746413<4/5`, not as a Lean theorem. The 4096-arc exact endpoints give strict rational lower margins `9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`, `1/100000000000000000`, `1/500000000000000000000` and simple upper bounds `1/100`, `1/1000000`, `1/4000000000`, `1/10000000000000`, `1/50000000000000000`, `1/100000000000000000000`; these are not Lean bounds on `e_n` until the path inclusions are proved.
- **Source differential identity, now compiled:** `contour51OriginalResponse_eq_sigmaXiLogDerivative` proves `R(z)=-(i/2)*xiLean'(s)/xiLean(s)` whenever the original continuation `F(z)` is nonzero, with `xiLean := sigmaCompletedXiParameter` and `s := operatorHeightParameter z`. It follows by differentiating the existing exact equality `F(z)=xiLean(s)` and using `ds/dz=i`; the axiom report is `[propext, Classical.choice, Quot.sound]`.
- Exact remaining analytic steps: verify the external Taylor/Cauchy remainder boxes as Lean bounds for the formal evaluator and prove the resulting complete-arc ranges enclose and integrate to the Lean lower-path integrals. The zeta/Gamma/digamma identity and its lower-path domain conditions are compiled. No finite mesh is a proof. The minimal next lemma for an unconditional first advance is `contour51ArbFirstThreeLowerPathResidualIntervalBounds`; all windows require all six path inclusions plus the uniform circle bound.
- Remainder distinction: the C2 omitted-material tail is the native finite-head omitted-index sum; `e_n=H_n-P_n` is the ten-mode residual proved equal to the normalized contour integral; the Arb Taylor/Cauchy remainder encloses evaluator truncation error on each arc and only supports the external path interval. C4's `|e_n|` bound is a separate contour norm estimate conditional on `hR`. No sign is inferred from either tail or Taylor remainder.
- C5 coordination: generic rational interval arithmetic, node evaluation, source normalization, and algebraic transport can be shared. The `d=0.0495` and `d=0.1` boxes do not enclose center values without a quantitative displacement map. No Bernoulli table or full set of zeta/Gamma nodes was duplicated in this work.
- Publication remains stacked on B2 PR #311. This update does not declare central positivity unconditional while the interval-transfer and C3 circle hypotheses remain open.

## Original source to explicit Arb evaluator — attempt 39

- **Compiled declarations:** `contour51SigmaXiLogDerivative_eq_zeta_gamma_factors`, `contour51GammaReal_logDeriv_eq_digamma`, `contour51SigmaXiLogDerivative_eq_arb_formula`, and `contour51OriginalResponse_eq_arb_formula`. Together with the previous `contour51OriginalResponse_eq_sigmaXiLogDerivative`, they prove the exact original-source response formula

  ```text
  R(z) = -(i/2) * (1/s + 1/(s-1) - log(pi)/2
                    + digamma(s/2)/2 + zeta'(s)/zeta(s)),
  s = operatorHeightParameter z.
  ```

  The source theorem assumes `F(z)≠0`, `0<Re(s)`, and `s≠1`. It derives `zeta(s)≠0` from `F(z)≠0` and the exact completed-zeta factorization. The xi derivative split and Gamma/digamma identity separately state `0<Re(s)`, `s≠1`, and `zeta(s)≠0` as needed.
- **Build:** Lean 4.32.0, `-DwarningAsError=true`, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`, exit 0. Log: `evidence/C3_SigmaContour51ArbContourBridge-attempt39-success.log`.
- **Axiom audit:** all four new theorems print only `[propext, Classical.choice, Quot.sound]`. Source audit found no `sorry`, `admit`, or declared axioms.
- **SHA-256:** Lean source `09d17f145e23a8909b26b947ebb7dce132c8a56c8800496cc76bd01301023595`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `159af9ebd6492cbddc9e825eec66a563f3d40f4e658bfd5cb75dbf85d4ab55d3`; successful log `20132739c7eb3779b12753f0710f332d69aafc8073a2a5f95f52395c2fa1a7cf`.
- **Still open at attempt 42:** prove that each external Arb/Acb complete-arc range contains this Lean evaluator including its Taylor/Cauchy remainder. The analogous 512-arc transfer to all points of the lower semicircle (and by oddness/evenness the full circle norm bound) also remains open. Attempt 44 below adds the exact integration adapter but does not transfer the Arb certificate; the certificate itself remains external.

## Lower-path evaluator domain — attempt 42

- **Compiled theorem:** `contour51OriginalResponse_eq_arb_formula_lower_path` proves the explicit original-source evaluator formula for every `u∈[0,1]` at `z=circleMap 0 51 (-πu)`. It obtains `F(z)≠0` from C1's boundary-zero exclusion, proves `0<Re(operatorHeightParameter z)` from the lower-semicircle sign of `Im(z)`, and proves `operatorHeightParameter z≠1` from `‖z‖=51`; the zeta nonvanishing premise is derived by the existing exact factorization.
- **Build:** Lean 4.32.0 with `-DwarningAsError=true`, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`, exit 0. The compiled log `evidence/C3_SigmaContour51ArbContourBridge-attempt42-success.log` prints only `[propext, Classical.choice, Quot.sound]` for the new theorem. Source audit found no `sorry`, `admit`, or declared axioms.
- **SHA-256:** current Lean source `261e76e006b78948bcf4d2c9cf326bdf543d2e7e04600ce9d76f5f3cbb59f8d1`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `a57b2d43c0851d69de965279803ea80de589591426d016cbf7c946188a7c4a26`; success log `e52110555ccb45d990bb6efc33aa35bb9f91a95aa47e36908aa5a2e6d455d34c`.
- **Minimum remaining lemma for the first unconditional advance:** prove `contour51ArbFirstThreeLowerPathResidualIntervalBounds` from the pointwise 4096-arc enclosures for `n=0,1,2`, the validated Taylor/Cauchy remainders, and their weighted rational sum comparisons, then apply the uniform-partition integration theorem. That single Lean transfer supplies `e_0,e_1,e_2` intervals to the already compiled determinant gate with margin `1/1000000000`; it needs no circle-norm or remainder-sign premise.

## Uniform-partition integration adapter — attempt 44

- **Compiled theorem:** `contour51_intervalIntegral_bounds_of_uniform_partition` states that if a continuous real-valued integrand on `[0,1]` lies between `lower k` and `upper k` on every closed arc `[k/N,(k+1)/N]`, then its interval integral lies between `(1/N)·Σ lower k` and `(1/N)·Σ upper k`. The proof uses interval-integral monotonicity on each arc and `sum_integral_adjacent_intervals`; it makes no Arb or decimal assumption.
- **Build:** Lean 4.32.0, `-DwarningAsError=true`, exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`, exit 0. Log: `evidence/C3_SigmaContour51ArbContourBridge-attempt44-success.log`. Its `#print axioms` entry reports only `[propext, Classical.choice, Quot.sound]`; the source has no `sorry`, `admit`, or declared axiom.
- **SHA-256:** current Lean source `6e0a0e00a98f7bdaf98aeb96a54a3bf0ac2bb87d112f5a041eb57f729f3fbc37`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `02c3dadd1b5ac7f0c402d29274ee6b34d0218e33a4d47a6d1c0c80a8b5830aa1`; success log `0801f83838f2ccefb00b5485b4b4f050e48d07d496157b91a49f351b2ad06cad`.
- **Limit:** the theorem handles only the real-variable integration and partition sum interface. The pointwise Arb-to-Lean evaluator enclosures, Taylor/Cauchy remainder proof, and rational endpoint-sum comparisons remain open.

## First-three 4096-arc rational integration — attempt 64

- **New compiled module:** `SigmaContour51ArbArcSumCertificate4096.lean` records the exact outward rational lower and upper endpoints on all 4096 arcs for `n=0,1,2`. It proves each of its six weighted `List.sum` expressions equals the exact rational exported by Arb and proves that these sums contain the stored aggregate interval endpoints. This is a formal arithmetic check of the external table; it does not prove pointwise evaluator inclusion.
- **New compiled bridge theorems:** `contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition` reindexes rational list endpoints as a finite equal partition and integrates them, given lower/upper pointwise bounds on every closed arc. `contour51ArbFirstThreeLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion` applies it to the original angular residual integrands for `n=0,1,2`. Its premise `contour51Arb4096FirstThreeArcEvaluatorInclusion` universally quantifies over all 4096 arcs and every `u` in each closed arc.
- **Theorem chain and current hypotheses:** `contour51OriginalResidualIntegral_eq_lower_path` is already unconditional from C1 and the source/path domain lemmas. Given the stated per-arc inclusion, the new bridge supplies `contour51ArbFirstThreeLowerPathResidualIntervalBounds`. The existing `completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals` then proves `1/1000000000 < sigmaPadeD 0 0`. The per-arc inclusion has not been proved, so this is not an unconditional positivity result. All-window positivity still additionally needs all six residual interval transfers and the uniform circle bound `‖R‖≤4/5` in Lean.
- **Absolute residual margins:** the exact lower margins for `e_0,…,e_5` remain `9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`, `1/100000000000000000`, and `1/500000000000000000000`. Their simple upper bounds are `1/100`, `1/1000000`, `1/4000000000`, `1/10000000000000`, `1/50000000000000000`, and `1/100000000000000000000`. These are proved comparisons against exact external endpoint rationals, not yet Lean sign theorems for the original residuals.
- **Arb versus C2 objects:** `e_n=H_n-P_n` is the original C2 source residual; C2 proves `H_n=P_n+e_n` and identifies `e_n` with the normalized Cauchy integral. The omitted-material tail in the C2 finite-head identity is separate. The Taylor/Cauchy remainder in the Arb evaluator only bounds evaluator truncation on an arc; after universal pointwise inclusion and integration, the full arc ranges bound `e_n`. No sign is assumed for either remainder. The determinant transfer retains `P_s e_(s+2) + e_s P_(s+2) - 2 P_(s+1)e_(s+1) + e_s e_(s+2) - e_(s+1)^2` in full.
- **Still open:** (1) prove the first-three all-points proposition `contour51Arb4096FirstThreeArcEvaluatorInclusion`, including validated Taylor/Cauchy remainder bounds; (2) perform the corresponding list-to-integral formalization for `n=3,4,5`; (3) transfer the 512-arc `‖R‖<4/5` certificate to a Lean theorem. The minimum next lemma for the first unconditional advance is item (1); the existing adapter and determinant gate discharge the remaining formal steps.
- **C5 boundary:** reusable pieces are rational interval arithmetic, fixed-node evaluation, original-source normalization, and algebraic source/coefficient transport. The displaced boxes at `d=0.0495` and `d=0.1` do not give central values without a quantitative displacement inclusion. No Bernoulli table or full zeta/Gamma node certification was duplicated.
- **Build and audit:** both new modules compile on Lean 4.32.0 with `-DwarningAsError=true`. The new sum theorem, list integration theorem, first-three conditional adapter, and existing determinant theorem report only `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, or declared axioms.
- **SHA-256:** arc-list Lean source `50a6b05f21154b1201312e7558ae169f8b6c3fc24ab40a8a77ef4bd14690b4de`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbArcSumCertificate4096.olean` `15bb4cb5a65c383b8e81d5058d17bcfcecef26f608c6f8447b700c67618be672`; success log `evidence/C3_SigmaContour51ArbArcSumCertificate4096-success.log` `0abf2281b0e672d0b08ff7dafe8e26ac9e7493987e6d3dce996450eeb7c5bb95`.
- **SHA-256:** contour bridge source `f791d581dadc1b779cf1ad6e14c12becff1de443baf7c9c6cc3e1bd71dd4be6d`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `155267b3d882b2d30f55b2a2adbfd3801876add5b2c22976feca845107dc842e`; success log `evidence/C3_SigmaContour51ArbContourBridge-attempt64-success.log` `55796b182bd19a5a98f431e24308cecd35a21fcade2627ed3291186f29bcc762`.
- **Arb evidence hashes:** full first-six per-arc JSON `8c6f603ad097a1e95ba7bc40e9134835b45c66ae4bd7790ea4b5bd240388bc81`; accompanying Arb log `e466153f1f9742eeae3ae02749461f0465c3ae95502657ef85b8b5431815f7c1`. The per-arc range exporter hash is `120c86c3adb6b776da6512585fcf7f31672b8b34056c9bd1841469daa6921ac1`; the Lean generator hash is `5645e1118d3985c3a52afe96957dd39d8bec627309e7fda8dccdcf31d76a5c89`.

## Updated C3 bridge — all six arc sums and conditional integral transfers

- **External Arb data:** `export_contour51_arc_ranges.py` exports outward exact rational intervals for all 4096 closed arcs and all six residual orders `n=0,…,5`, using python-flint/Arb 0.8.0, 160-bit precision and Taylor degree 32. The exact weighted sums were independently compared to the recorded aggregate endpoints before export. This is rigorous external interval arithmetic, but the artifact is not itself a Lean proof that the evaluator is contained in every per-arc interval.
- **Compiled arithmetic module:** `SigmaContour51ArbArcSumCertificate4096.lean` proves the lengths and exact rational sums of all six lower/upper arc lists, and `contour51Arb4096AllSixWeightedRecordedBounds` proves the twelve weighted comparisons against the six stored aggregate intervals. The smaller first-three aggregate theorem remains available for the direct `s=0` determinant gate.
- **Compiled bridge module:** `SigmaContour51ArbContourBridge.lean` proves `contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion` and `contour51ArbAllSixLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion`. Thus, if every per-arc box contains the real part of the original source evaluator on its full closed parameter interval, then all six original lower-path integrals lie in the recorded Arb intervals. The first-three adapter and `completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals` are also compiled; the latter gives the absolute margin `1/1000000000` once those first three integral intervals are supplied.
- **Already compiled source/contour facts:** the exact original response equals the Arb zeta/Gamma/digamma formula throughout the lower semicircle, with the zero-free and domain conditions derived from C1 and path geometry. The full-circle normalized residue integral equals the lower-path integral, and continuity, integrability, orientation, parity, and uniform-partition integration are proved. The original C2 residue identity identifies `e_n=H_n-P_n` with this normalized integral for the same fixed ten-mode list.
- **Exact open hypotheses:** (1) prove `contour51Arb4096AllSixArcEvaluatorInclusion`, including a Lean enclosure of the original evaluator and the validated Taylor/Cauchy remainder on every one of the 4096 complete arcs; (2) transfer the independent 512-arc certificate to Lean as the uniform circle bound `‖R z‖≤4/5` for every `‖z‖=51`. The first hypothesis restricted to `n=0,1,2` is the minimum next lemma for the first unconditional determinant result. No remainder-sign assumption is added.
- **Margins:** exact endpoint comparisons permit lower margins for `e_0,…,e_5` of `9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`, `1/100000000000000000`, and `1/500000000000000000000`; simple upper bounds are `1/100`, `1/1000000`, `1/4000000000`, `1/10000000000000`, `1/50000000000000000`, and `1/100000000000000000000`. Until the open pointwise inclusion is proved, these are comparisons to external endpoints, not Lean sign theorems for the source residuals. No unconditional central positivity is claimed.
- **C5 coordination:** reusable pieces are rational interval arithmetic, fixed-node evaluation, original-source normalization, and the algebraic `d=0` source/coefficient transport. Boxes at `d=0.0495` and `d=0.1` still need a quantitative transformation to enclose center values. This work did not duplicate the Bernoulli table or all zeta/Gamma nodes and did not access C5's worktree or cache.
- **Lean audit:** both modules compiled sequentially on Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, with `-DwarningAsError=true`. The reported theorem dependencies are only `[propext, Classical.choice, Quot.sound]`. A scan of both Lean sources found no `sorry`, `admit`, or declared axiom. The C2 output root is `/home/thlinux/tmp/c2-contour51-20261108-lean432`; OLean files remain there, not in the repository.
- **SHA-256:** six-arc Lean source `82f22ef5735c9e5f458e66724bd61cfd5949c590581a33473b0b3b3bcf4d5add`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbArcSumCertificate4096.olean` `b0efcc78bb06b9c8b8885ec1fb3cc0b301796a025a76fcb76b3fc579df1898c9`; success log `evidence/C3_SigmaContour51ArbArcSumCertificate4096-success.log` `435e444244530344c7a32e01d6716c91edd0e9eafc01a3457565e2e6230eb50b`.
- **SHA-256:** bridge source `c3e51b55925c17028d5965dc6eea3e27cee200aeaad8fbd983f94c13a6a0fb72`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `376f099abac1a91fba27d46a99f16770be798eb665321c5eb09fde959ec3e851`; success log `evidence/C3_SigmaContour51ArbContourBridge-attempt66-success.log` `6a5cf742810fc787ff000204836f746f4eac10d236de4b1ea9ca3eb2f89c0700`.
- **SHA-256:** exporter `120c86c3adb6b776da6512585fcf7f31672b8b34056c9bd1841469daa6921ac1`; generator `bad8f9a306f14226e8b7862015aaa80f6c930530bfdb4279301df80bc7b39329`; per-arc JSON `8c6f603ad097a1e95ba7bc40e9134835b45c66ae4bd7790ea4b5bd240388bc81`; Arb log `e466153f1f9742eeae3ae02749461f0465c3ae95502657ef85b8b5431815f7c1`.

## Incremento — cota de semicircunferência implica cota no círculo

- **Teorema compilado:** `contour51OriginalResponse_circle_norm_bound_of_lower_semicircle_uniform_bound` em `SigmaContour51ArbContourBridge.lean`. Sua hipótese explícita `contour51ArbLowerSemicircleUniformResponseBound` quantifica todo `u∈[0,1]` e limita `‖contour51OriginalResponse (circleMap 0 51 (-π*u))‖` por `4/5`. A conclusão é a cota correspondente em `Metric.sphere 0 51`. A redução usa `image_circleMap_Ioc`, periodicidade de `circleMap` e o teorema compilado de imparidade da resposta original. A resposta permanece `-F'/(2F)` para `F=completedNativeCharacteristicContinuation`.
- **Fronteira da prova:** a hipótese não foi descarregada. O Arb/Acb disponível certifica externamente os 512 arcos e o máximo `<0.746413<4/5`, mas ainda falta em Lean a inclusão da função original nas caixas de cada arco, incluindo os restos Taylor/Cauchy. Portanto `hR` de C4 permanece aberto.
- **Fonte e resíduos:** a fórmula zeta/Gamma/digamma da resposta no caminho inferior, as condições de domínio/zero-livre e a identidade C2 do integral do kernel meromorfo com `e_n=H_n-P_n` continuam compiladas. O resto do avaliador Arb só passa a controlar `e_n` após a inclusão ponto a ponto e integração; ele não é a cauda material da soma finita C2 nem o próprio resíduo dos dez modos.
- **Estado exato das hipóteses:** (1) inclusão uniforme da resposta nos 512 arcos para obter a premissa semicircular e, por este teorema, `hR`; (2) `contour51Arb4096AllSixArcEvaluatorInclusion` nos 4096 arcos para os seis integrandos residuais, incluindo os restos. A restrição do item (2) a `n=0,1,2` é o lema mínimo para o primeiro avanço incondicional: o adaptador compilado dá os três intervalos e o gate dá `1/1000000000 < sigmaPadeD 0 0`. Nenhuma positividade central incondicional é afirmada.
- **Margens Arb ainda externas a Lean:** `e_0≥9/1000`, `e_1≥9/10000000`, `e_2≥9/50000000000`, `e_3≥1/25000000000000`, `e_4≥1/100000000000000000`, `e_5≥1/500000000000000000000`. Os limites superiores simples são, respectivamente, `1/100`, `1/1000000`, `1/4000000000`, `1/10000000000000`, `1/50000000000000000`, `1/100000000000000000000`. São comparações Lean com extremos racionais externos; os sinais dos seis `e_n` seguem condicionais até a inclusão ser provada.
- **Build/auditoria:** módulo recompilado sequencialmente em Lean 4.32.0 com `-DwarningAsError=true`, usando o output isolado `/home/thlinux/tmp/c2-contour51-20261108-lean432`, enquanto C5 compilava em seu worktree/cache separado autorizado. A memória disponível era 52 GiB. O `#print axioms` do teorema novo retorna `[propext, Classical.choice, Quot.sound]`; busca no fonte não encontrou `sorry`, `admit` ou declarações `axiom`.
- **Hashes SHA-256:** fonte `a9850315d69db925621a61cb4ac691ab65a66a1854f1226528ebaab0e1dc1a07`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbContourBridge.olean` `043d215f168741637f1e5b31eb8597a2d5733ce3211738e7273b9c244c6d89c1`; log `evidence/C3_SigmaContour51ArbContourBridge-attempt68-success.log` `86dd46a098135dbeac5beda5877b2c4868671144ddb8f94f38147fe2a229c272`.
- **Próximo passo técnico mínimo:** o script C3 monta `ζ`/`ζ′` com Taylor de ordem 32 e raio `1/4`, controla os restos por Cauchy, depois combina com caixas para `s`, `s-1`, `log π` e digamma. Os CSV/JSON guardam os extremos finais por arco, sem o rastro racional detalhado dos coeficientes Taylor e operações intermediárias. É necessário fornecer a Lean as inclusões por arco de `ζ` e `ζ′` com coeficientes/majorantes certificados e compor as caixas para a resposta/integrando. A primeira restrição útil é nos 4096 arcos para `n=0,1,2`; a cota da resposta usa separadamente os 512 arcos.
- **Componentes C5 reutilizáveis identificados:** bolas reais e transporte racional (`SigmaFiniteRationalIntervals.lean`, `SigmaFiniteRationalIntervalTransport.lean`); tipo `ComplexInterval` e avaliação pontual (`SigmaC5RationalNodeEval.lean`); caixa formal de `log π` (`SigmaC5PiInterval.lean`); recorrência/normalização da fonte (`SigmaSourceBezout.lean`, `SigmaContour51BoxSensitivity.lean`). C5 ζ é avaliada apenas em nós racionais perto de `1/2`, sem ζ′ ou Taylor para retângulos, e Gamma em nós fixos não fornece digamma contínuo no contorno. A conversão exata do `log π` já compila em `SigmaContour51C5PiBridge.lean`; nenhuma tabela Bernoulli ou lista de nós zeta/Gamma foi refeita. Transporte de nó ainda requer transformação quantitativa de centro e caixa.

## C3 genérico — restos de Taylor/Cauchy e transferência intervalar

- **Módulo:** `research/native-moving-schur-sigma/SigmaContour51TaylorRemainder.lean`.
- **Teoremas compilados:** `contourTaylorCoefficient_norm_le`,
  `contourTaylorDerivativeCoefficient_norm_le`,
  `contourTaylorWeightedGeometricShift_sum`, `contourTaylorRemainder_norm_le`,
  `contourTaylorDerivativeRemainder_norm_le`, `contourTaylorIntervalPolynomial_contains`,
  `contourTaylorIntervalPolynomial_inflate_contains` e
  `contourTaylorDerivativeIntervalPolynomial_inflate_contains`.
- **Hipóteses:** Cauchy exige `DiffContOnCl ℂ f (ball c r)` e `‖f w‖≤M` na esfera; o resto da
  derivada exige também `DifferentiableOn ℂ (deriv f) (ball c r)`. Ambos requerem `z∈ball c r`,
  `0≤q<1` e `‖z-c‖≤q*r`. A transferência por caixas exige caixas explícitas contendo cada
  coeficiente Taylor exato e o deslocamento, além de um erro racional. Esses dados não foram ainda
  provados para os arcos Arb atuais.
- **Fórmulas verificadas:** `M*q^(N+1)/(1-q)` para a cauda do valor e
  `(M/r)*q^N*((N+1)-N*q)/(1-q)^2` para a cauda da derivada. Correspondem a `N=32`, `r=1/4` do C3.
- **Build:** Lean 4.32.0, `-DwarningAsError=true`, saída exclusiva em
  `/home/thlinux/tmp/c2-contour51-20261108-lean432`, código de saída 0. Comando em
  `evidence/BUILD_COMMANDS.md`; log compilado em
  `evidence/C3_SigmaContour51TaylorRemainder-success.log`.
- **Axiomas:** os oito teoremas reportam somente `[propext, Classical.choice, Quot.sound]`. A
  varredura do fonte não encontrou `sorry`, `admit`, `native_decide` nem axioma declarado.
- **SHA-256:** fonte `994530cf7c4159c423ee099a8cfeca814e91fa964c66caa37381d2bb07336769`; OLean
  `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51TaylorRemainder.olean`
  `77b9e6bd16b8fe309aa6be1595441dec7d9101db6ee3fb7136154b90b61a67ee`; log
  `32525b93029267fbccbb71850e719d7b69707e06ce34cc061241bae28ad961c5`.
- **Limite atual:** o módulo não certifica caixas de coeficientes, majorantes de disco ou
  deslocamentos a partir dos dados Arb. As inclusões dos 512/4096 arcos e os sinais dos resíduos
  continuam abertos; nenhuma positividade central incondicional foi concluída.

## C3 — limites superiores verificados para os 512 arcos

- **Exportação:** `generate_contour51_bound_lean.py` lê `response_upper` do CSV C3 em python-flint 0.8.0 a 160 bits e converte a ponta superior de cada bola Arb em fração racional outward-rounded. São 512 entradas ordenadas. A maior é `1866031173444015023751641117317496301922252635655657/2500000000000000000000000000000000000000000000000000`.
- **Prova aritmética:** `SigmaContour51ArbBoundCertificate512.lean` prova que cada extremo está `≤746413/1000000<4/5`, e que os 512 arcos fechados cobrem `[0,1]`. Sob `contour51Arb512ResponseArcEvaluatorInclusion`, deriva a cota uniforme no caminho inferior e em toda a esfera. O teorema `completedNative_sigmaPadeD_pos_of_contour51_512_arc_inclusions` compõe a cota com o teorema C4/C6, mas mantém os seis sinais `e_n≥0` explícitos.
- **Prova ainda aberta:** `contour51Arb512ResponseArcEvaluatorInclusion` não foi descarregada. O certificado externo usa Taylor de ordem 32, raio `1/4` e restos Cauchy; os artefatos atuais não têm rastro racional suficiente para provar em Lean a inclusão da função em cada caixa. Portanto o máximo externo `<0.746413` ainda não fornece `hR` incondicional em Lean. As inclusões de resíduos nos 4096 arcos continuam uma obrigação separada.
- **Auditoria:** Lean 4.32.0, `-DwarningAsError=true`. Os teoremas novos da tabela e das pontes dependem apenas de `[propext, Classical.choice, Quot.sound]`; não há `native_decide`, `sorry`, `admit` ou axiomas novos.
- **Tentativas:** tentativa 1 interrompida após 11 minutos porque `interval_cases` repetia a expansão da lista; tentativas 2–4 corrigiram problemas de tipo, cobertura e conversão; tentativa 5 compilou a tabela e a ponte para `hR`; tentativa 6 compilou também a composição com o teorema condicional de todas as janelas. Logs preservados: `C3_SigmaContour51ArbBoundCertificate512-attempt{1,2,3,4,5}*` e `C3_SigmaContour51ArbBoundCertificate512-success.log`.
- **Hashes SHA-256:** CSV `c1a2a37fcd1450c34181edd0f6fe7fac334fdf750be153d708c15f2e0fb90519`; gerador `c3c2cc6177c9ef6989e60b52e9a8aabb2bb6be35a37aeb555d229800a9a17669`; Lean `22a6736ab5be93fe62cdf770cd28b29bd539ab9ef7b8c7a8ec8ceec44ff8f159`; OLean `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbBoundCertificate512.olean` `daad771c67482b650de324b9b517319f62fa59a032831a9724bd58916e1d9eba`; log `evidence/C3_SigmaContour51ArbBoundCertificate512-success.log` `8e5943ed413bedfba206d8605249ec3e37839c1deeb4f21755500585c5dba952`.

## C3 — tabela única de coeficientes Taylor para ζ e ζ′

- **Teorema algébrico compilado:** `contourTaylorCoefficient_deriv_eq_nat_mul` prova, para toda
  função complexa `f`, centro `c` e índice `k`, a identidade
  `contourTaylorCoefficient (deriv f) c k = (k+1) * contourTaylorCoefficient f c (k+1)`.
- **Transporte por caixas compilado:**
  `contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_contains` usa caixas dos
  coeficientes de `f` até `N` e uma caixa de `z-c` para conter o polinômio Taylor de `deriv f` com
  `N` termos. `contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_inflate_contains`
  infla por um erro racional e contém `deriv f z` quando o limite desse resto foi provado. O
  teorema `contourTaylorCauchyValueAndDerivativeBoxes` combina a caixa Taylor de `f`, a caixa do
  polinômio derivado e os dois limites racionais de Cauchy para concluir simultaneamente as
  inclusões de `f z` e `deriv f z`. Isso permite compartilhar a tabela de coeficientes de ζ do
  Arb com ζ′, como faz `acb_series.zeta()`.
- **Hipóteses exatas:** as provas de transporte recebem
  `∀ k≤N, coeff[k] contém contourTaylorCoefficient f c k`, `deltaBox contém delta`, a igualdade
  `delta=z-c` e limites racionais que majoram os dois restos. O teorema combinado exige ainda
  `0<r`, `DiffContOnCl` de `f` no disco, `DifferentiableOn` da derivada no disco, majorante `M`
  na esfera, `0≤q<1`, `z∈ball c r` e `‖z-c‖≤q*r`. O módulo não prova as caixas de coeficientes,
  analiticidade de ζ nos discos, majorantes ou deslocamentos.
- **Build e audit:** Lean 4.32.0, `-DwarningAsError=true`, saída exclusiva
  `/home/thlinux/tmp/c2-contour51-20261108-lean432`, exit 0. Os quatro teoremas novos reportam
  somente `[propext, Classical.choice, Quot.sound]`. O fonte não contém `sorry`, `admit` ou
  declarações de axioma. Tentativas 1 e 3 falharam durante o desenvolvimento; tentativa 2 foi
  uma compilação intermediária; tentativa 4 é a compilação final e está registrada em
  `evidence/C3_SigmaContour51TaylorCoefficientBridge-success.log`.
- **SHA-256:** fonte
  `1bb5426aa763ab9aa424616a97c228f78db89faf9b5edd5aebd3941b5413bc1a`; OLean
  `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51TaylorCoefficientBridge.olean`
  `bcb295f9026adc25446d5acbb458a5733136512096cf70df3f8165a67d225c98`; log de sucesso
  `7fb07ce21c0d26ac866751d4ef11aaaef81a4848152b0a72335e3bb24873fddf`.
- **Limite:** os certificados atuais não exportam caixas racionais dos coeficientes Arb, discos,
  restos ou caixas dos demais componentes. Nenhuma inclusão de 512/4096 arcos, sinal `e_n`, `hR`
  ou positividade central incondicional resulta deste incremento. O próximo lema para o primeiro
  avanço é a inclusão uniforme dos componentes Taylor da fonte nos arcos 4096 para `n=0,1,2`,
  incluindo a validade analítica e as caixas exatas dos coeficientes.

## C3 — reutilização da caixa C5 para `log π`

- **Módulo compilado:** `SigmaContour51C5PiBridge.lean` define
  `contour51C5LogPiBox` a partir de `c5PiLogInterval 160` e prova
  `contour51C5LogPiBox_contains : contour51C5LogPiBox.contains
  (Complex.log (Real.pi : ℂ))`. A prova reutiliza `c5_pi_log_interval_contains` e `Complex.ofReal_log`;
  não refaz a série de Machin nem a avaliação intervalar de logaritmos de C5.
- **Fronteira C5 conferida:** `c5RationalZetaNodeBox_contains` e
  `c5RationalZetaCenteredNodeBox_contains` certificam ζ apenas em nós racionais exatos próximos
  a `0.5+0i` (`a∈[2/5,3/5]`, `b∈[0,128/100000]`), sem caixas de retângulo contínuo, ζ′ ou
  coeficientes Taylor. Os certificados C5 de Gamma são nós fixos e não limitam a variação de
  digamma sobre `s/2`. A aritmética intervalar, a normalização/transporte da fonte e a caixa de
  `log π` são reutilizáveis; os nós zeta/Gamma/Bernoulli C5 não foram duplicados.
- **Build e audit:** `SigmaC5PiBounds`, `SigmaC5PiInterval` (dependências C5 reutilizadas) e
  `SigmaContour51C5PiBridge` foram compilados sequencialmente em Lean 4.32.0, com warnings como
  erros, no output isolado `/home/thlinux/tmp/c2-contour51-20261108-lean432`; a última compilação
  saiu com código 0. O `#print axioms` do teorema novo retorna somente
  `[propext, Classical.choice, Quot.sound]`. O novo fonte não contém `sorry`, `admit` nem axioma
  declarado. Tentativa 1 falhou apenas na prova de contenção do zero da caixa imaginária; tentativa
  2 é a compilação final.
- **SHA-256:** fonte do bridge
  `4cd5f6d5faed5d3eca007d1929204b801daf7aaf8d3d02b42b658b4b1a68db41`; OLean
  `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51C5PiBridge.olean`
  `5d48fa605f104ea61bdf83f221e712864d3c07fc46a64beac3865ab8687a7ea0`; log final
  `9942fa920300110a7d756364905bf17ce5b42a110d6bc258bf48d4924d03e97a`. C5 source/OLean hashes:
  `SigmaC5PiBounds.lean` `b38d68df2ddbe6728218db09e9661980a7bf635398528a840ae129fe4bdc3f97`, imported OLean
  `b15b9adb144e0965201bbd51dbfdadb10fa0384af5a532683c8b8ab50358322f`;
  `SigmaC5PiInterval.lean` `6d0ad33d4a25c65a9b469c3ef0535e00f6e2e6675ec9524cbe02716391835488`, imported OLean
  `188d70193c2c530339df6e1b371490657efa570d3238607ca0a32b3d5646b8f0`.
- **Limite:** esse resultado preenche uma caixa constante da fórmula de resposta, mas não certifica
  ζ, ζ′, digamma, `s(u)`, os denominadores por arco ou suas comparações com os endpoints Arb. As
  inclusões `contour51Arb4096FirstThreeArcEvaluatorInclusion` e
  `contour51Arb512ResponseArcEvaluatorInclusion` continuam abertas; nenhuma margem de `e_n` ou
  positividade central se torna incondicional.
