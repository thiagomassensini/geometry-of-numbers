# Proveniência das fontes e entradas do build C1

## Pins e toolchain

- Base de Geometry após o merge de C0: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib no Geometry e no manifesto Carry: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Fontes Carry usadas pela prova: `carry-self-adjoint-operator@045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Manifesto Carry: Geometry `d7cc54f5c485320f1fada33118e9e6101488819a`, NativeCarryC3Crosswalk `150cfc7fb08da96bf8117f15869cc2b819d593c2`, CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`, NativeCarrySpectralWeyl `298d83c9351e308a5213b9f5ac32e44087f98a9f`, FiniteNativeCarryOperator `00e9d6beb17226545abf5ddf90bbfede6c7146b0`.
- O checkout disponível de Carry está em `8f15ec76e5a95eb0c61da3a114729363a1d6a477`, com arquivos locais de outros trabalhos preservados. Nenhum desses arquivos foi alterado.
- Fontes do certificado de primeiro zero: `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, com avisos de licença e `lean432-compat.patch` preservados.
- `check_c1_pins.py` auditou recursivamente 1.278 módulos-fonte não-Mathlib alcançáveis a partir da cadeia C1. Carry (891), CPFormal (167), NativeCarrySpectralWeyl (41), GreenFrame (41), Geometry (110), NativeCarryC3Crosswalk (26) e FiniteNativeCarryOperator (2) conferem byte a byte com seus pins. Resultado em `c1-source-pin-audit.txt`.

## Fontes Lean reaproveitadas

- `SigmaZeroObstruction.lean`, `MomentLogConvexity.lean` e `MomentComplexification.lean` foram copiados byte a byte da branch `agent/native-moving-schur-sigma` em `9392ebac9930f5d11c56f595556080e8ab1de809`.
- `SigmaNativeContinuation.lean` foi copiado byte a byte da integração Lean 4.32 em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
- `SigmaNativeZeroBridge.lean` extrai os corpos originais de `sigmaNativeCompletionFactor_ne_zero_of_strip` e `completedNativeCharacteristicContinuation_zero_iff_zeta` de `SigmaRHHeightBridge.lean` no mesmo commit de integração. A prova resultante não importa a contagem completa de altura 50, as caixas extras nem a recuperação Padé.
- `SigmaCertifiedNegativeDirection.lean` compõe `HardyFirstZero.first_zero_on_line`, `sigmaLineZero`, `operatorHeightParameter`, as duas pontes no strip e a obstrução condicional em `sigmaMatrix`.
- O fechamento mínimo da certificação contém quatro fontes `ZetaLean` e seis fontes `HardyFirstZero`. As dez fontes conferem com a integração de altura 50 citada. Nenhum `.olean` de Lean 4.35 foi copiado.

## Fronteira de compilação

- `lake build --wfail` na raiz compilou o checkout Geometry completo: a primeira execução em cache ausente concluiu 8.857/8.857 jobs; a saída capturada em `c1-root-build.log` é uma execução incremental posterior, também bem-sucedida (8.850 jobs).
- `compile_c1.sh` recompila para `/tmp/sigma-c1-certified-20261105` os módulos locais da camada Schur, Sigma e jets, os quatro módulos Sigma copiados/portados, a ponte e o corolário. Compila ainda o fechamento mínimo do certificado de primeiro zero, com warnings-as-errors.
- O cache GreenFrame do pin estava sem alguns artefatos necessários pela cadeia Carry. O roteiro compilou cinco fontes GreenFrame (`NormalizedSplit`, `ExternalRange`, `StaticPoisson`, `RestrictedGraph`, `AmbientPoisson`) para o diretório de build desse pacote pinned, sem modificar fontes ou arquivos rastreados do pacote.
- A compilação focada consome os `.olean` das dependências externas Lean/Mathlib/Carry de seus caches `.lake` versionados. Portanto é uma compilação focada das fontes C1 e de seu fechamento Geometry/certificado, com proveniência fonte recursivamente auditada; não é uma reconstrução limpa de todos os artefatos externos.
- O log final está em `c1-focused-build.log`. `check_c1_axioms.py` aceitou 106 relatórios. Corolário C1 e `HardyFirstZero.first_zero_on_line` dependem somente de `propext`, `Classical.choice`, `Quot.sound`.
- A varredura proibiu `sorry`, `admit`, `native_decide`, `sorryAx` e declarações `axiom` customizadas nos fontes C1.
- Hashes SHA-256 de fontes, scripts, avisos e patches estão em `c1-source-sha256.txt`.

## Limite matemático

A conclusão é sobre `sigmaMatrix d 0 N` e `completedSigmaLogJet` originais. Não usa `twoPoleMoment`, não afirma positividade central e não conclui persistência para todas as dimensões maiores; essa extensão é C1B.
