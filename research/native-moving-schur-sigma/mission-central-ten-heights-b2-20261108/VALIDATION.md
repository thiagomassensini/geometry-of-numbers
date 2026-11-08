# B2 validation ledger

## B2.0

- Created a dedicated Git worktree and branch from B1 PR #304 head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Reserved the exclusive output root `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- Confirmed PR #304 is open and mergeable; its branch was not changed.
- C5 prefix128 was active during initial inspection. Its later Lean build ran in a separate worktree and cache; B2 waited until it exited. All C5 paths remained read-only and unused by B2.

## B2.1

- Source: `SigmaHeight50Integration.lean`
- Public export: `CarrySigmaObstruction.sigmaHeight50_ten_zero_witnesses_and_count`.
- Build: `SigmaHeight50Integration` with Lean 4.32.0 and `-DwarningAsError=true`; command in `evidence/BUILD_COMMANDS.md`.
- Axiom report for the exported theorem: `[propext, Classical.choice, Quot.sound]`.
- Source SHA-256: `ce0484a1b6095dfce55dab760ae0cc7e5c4748680165500bbb54d907b7fce98e`.
- OLean SHA-256: `c38181ccab55b622c36623ac97bebeff82909339d1490377cdf5efcb1c360f6c`.
- Successful log SHA-256: `5cff691bc59b2f7ee03e5c89b665739d150933b52925c7158541bf2de9bfba35`; see `evidence/B2.1-SigmaHeight50Integration.log`.
- First attempt stopped before elaboration because `RHHeight.Main` was not on `LEAN_PATH`; the corrected command adds the read-only `c2/external` artifact directory. Failed-attempt log SHA-256: `828e9782a52ceb0fc4b9827e2eabbe2dd693641628ab88e432e0162fc4a5403f`; see `evidence/B2.1-SigmaHeight50Integration-attempt1.log`.

## B2.2

- Source: `SigmaCentralTenHeightScaleBridge.lean`.
- Public certificates: `CarrySigmaObstruction.sigmaHeight50_ten_height_scales` and `CarrySigmaObstruction.exists_sigmaHeight50_scale_hbox`.
- The first theorem preserves the B2.1 `γ` and `ts` witnesses and binds `a i` to `((ts i)^2)⁻¹`. It proves positivity for all ten scales, both exact rational bounds for every index, and `a 0 > a 1 > 0`. The second theorem returns B1's `hbox` directly with no premises.
- Build: Lean 4.32.0, `-DwarningAsError=true`; command in `evidence/BUILD_COMMANDS.md`.
- Both transitive axiom reports: `[propext, Classical.choice, Quot.sound]`.
- Source SHA-256: `700f0163b6617737e18f89bb7688d9729d1782fc8dbd76249194a803800770ef`.
- OLean SHA-256: `d476cbab5d85e3557332787005550891ab269a654568d615acce92f5ab53eaf3`.
- Successful log SHA-256: `69230e90636a6ece8fe5e35de2d75755c481ee9b62ae30ef95fc549ed865742a`; see `evidence/B2.2-SigmaCentralTenHeightScaleBridge.log`.
- Two failed attempts are preserved: the first used invalid Lean superscript syntax; the second exposed leftover superscript syntax in a helper and an argument-order mistake while proving positivity of the sum. Neither produced a successful OLean. Their log hashes are `c74bfca288988ed3103d69c94aa09d64c1603a8511730c148f174e1a2c69c860` and `8e1c069df0155b78e35a2a07e0d45df8eb3e45a0814c40e6287e0e8b4a9c864f`.

## B2.3

- Source: `SigmaCentralTenHeightRootBridge.lean`.
- Public theorem: `CarrySigmaObstruction.sigmaHeight50_original_characteristic_roots`. It transports the ten supplied positive zeta roots and their order-one property to `completedNativeCharacteristicContinuation`, obtains the negative roots and their order-one property by evenness, and uses the distinct-point count to classify every continuation root with `|Re w| ≤ 50` as one of the signed ten heights.
- Build: Lean 4.32.0, `-DwarningAsError=true`, exit status 0; exact command in `evidence/BUILD_COMMANDS.md`.
- Transitive axiom report: `[propext, Classical.choice, Quot.sound]`.
- Source SHA-256: `7831cf58dc8cdeab4b98cd93ccbe6c1f8cedec2383130ef7edd6dd68d41f863e`.
- OLean SHA-256: `e5ec3b6565d4c1757219c352ec56af8f405907472b2efe4f201651bf60f01e90`.
- Successful log SHA-256: `2c742c5f2bd0db03a04c3c7fa3611f3486f76b7818d7285facf5b5ce9b944242`; see `evidence/B2.3-SigmaCentralTenHeightRootBridge.log`.
- Two failed namespace-resolution attempts are preserved. Attempt 1 hash: `b5e55e6fe20d3f53cfc7b3d5538064766f007fcd78ae0fd2d96b1ee9052ccd7f`; attempt 2 hash: `a603da7040e896db59000463f1b90d33f50ea36ecfef90e565d4b73e512fa4a5`.

## B2.4

The fail-closed audit requires both scale theorem reports and the original-characteristic root theorem report, rejects unexpected axioms and malformed/missing reports, and scans all three B2 source modules for `sorry`, `admit`, `native_decide`, and any `axiom` token.

- Command: `python3 research/native-moving-schur-sigma/mission-central-ten-heights-b2-20261108/evidence/check_b2_scale_root_axioms.py`; exit status 0.
- Result: exactly three required scale/root reports accepted; all report only `[propext, Classical.choice, Quot.sound]`; all three B2 source files pass the forbidden-token scan.
- Checker source SHA-256: `ef94563c48a223d16935d3e503cf999ee1c31de553518db8413edd9a46c134ec`.
- Checker output SHA-256: `6c79ac002198b2f93b20d023605aee54ce7a7e256c553d35588e99b745b56e36`; see `evidence/B2.4-check_b2_scale_root_axioms.log`.
- Exact command is also recorded in `evidence/BUILD_COMMANDS.md`.
- B2 PR [#311](https://github.com/thiagomassensini/geometry-of-numbers/pull/311) is open and mergeable against B1 PR #304's branch `agent/c2-central-hankel2-allorder-20261107`; the B2 branch is five commits ahead and contains no B1 changes.

## Build isolation

Existing C2/height-50 integration artifacts are read-only inputs; no C2/C3 build restart is permitted. The B2 Lean outputs remain in `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
