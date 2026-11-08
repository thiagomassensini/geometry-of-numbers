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

## B2.3–B2.4

Pending. Existing C2/height-50 integration artifacts are read-only inputs; no C2/C3 build restart is permitted.
