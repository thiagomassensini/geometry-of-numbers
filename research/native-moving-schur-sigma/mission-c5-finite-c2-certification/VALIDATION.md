# C5 — validação

**Status atual:** Fase 1 de transporte algébrico provada e auditada. A verificação racional dos JSONs e a geração intervalar foram reproduzidas. As fases de verificação racional Lean e inclusão intervalar da fonte ainda não estão fechadas.
**Toolchain:** `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
**Base geometry:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776`.
**Fonte C4 compilada:** source hashes de `SigmaSourceBezout.lean`, `SourceBezout.lean`, `SigmaPadeCorrespondence.lean` e `SigmaZeroObstruction.lean` conferem com `origin/main`; pins completos em `evidence/pins-and-sha256.txt`.

## 1. Transporte algébrico Lean — PASSOU

Arquivos novos:

- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean`
- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransportAudit.lean`

A prova começa em `completedSigmaDisplacedSource_coefficient_recurrence` de C4 e mantém `completedSigmaDisplacedMoment = 2*completedSigmaLogJet`. O módulo prova a recorrência polinomial sem divisão, a identidade do menor escalado com `CarrySigmaPade.sigmaPadeD` original e os dois lemas de transferência de sinal usando `completedSigmaDisplacedSourceCoefficient_zero_pos`.

O build final foi feito para diretório de saída novo, com warnings tratados como erros, usando o script `compile_sigma_pade.sh`. Os logs e o comando exato estão em `build-transport-clean.log` e `transport-build-record.md`.

`#print axioms` para os quatro teoremas auditados lista apenas `propext`, `Classical.choice` e `Quot.sound`. Saída em `axiom-audit-transport-clean.log`. Nenhum axioma próprio, `sorryAx` ou `admit` foi introduzido.

## 2. Genealogia da fonte — conferida, preservada

A revisão carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, em `CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean`, prova
`canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar`:

```text
finiteBracketCharacteristic 2 cutoff s
  + ∑' index, centerBracketTerm 2 s (index + cutoff)
  = factor 2 s * nativeScalar s
```

O gerador numérico C5 avalia a mesma cabeça C2 mais cauda exata. Hurwitz é usado somente para avaliar a soma exata omitida; depois o fator nativo C2 e a completação original são aplicados. C4 liga os coeficientes resultantes aos jets originais. Hash da ponte carry e demais fontes em `pins-and-sha256.txt`.

## 3. Verificação racional condicional — PASSOU

O verificador `verify_signs_exact.py` usa `fractions.Fraction`; não usa Float para decidir sinal. Resultados nos JSONs rastreados:

| Deslocamento | Sinais condicionais | Log |
|---|---|---|
| `99/2000` | `+++++++++++-` | `interval-certificate/verify-d00495.log` |
| `1/10` | `+++++++++-` | `interval-certificate/verify-d01.log` |

Esses cálculos provam os sinais supondo as inclusões de todos os coeficientes nas caixas.

## 4. Geração intervalar — REPRODUZIDA, não é ainda prova formal

As três configurações pedidas passaram após uma correção apenas de compatibilidade de backend, registrada como patch:

1. `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`; sinais `+++++++++++-`.
2. `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`; sinais `+++++++++++-`.
3. `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`; sinais `+++++++++-`.

Cada saída foi conferida pelo verificador exato em um segundo passo. JSONs e logs de geração e verificação estão em `interval-certificate/`.

A primeira execução falhou antes de produzir JSON porque esta instalação do `mpmath 1.3.0` seleciona `gmpy2.mpz`, que `Decimal` não aceita. A falha foi preservada em `sign1024_stirling-initial-gmpy2-failure.log`. No checkout Momentos isolado foi testada uma conversão explícita `int(mpz)`; o patch correspondente está versionado ao lado. A branch remota da PR #2 não foi alterada.

O avaliador permanece experimental: as funções elementares `mpmath.iv` e sua garantia de arredondamento externo não foram provadas em Lean. Portanto, as caixas ainda não são inclusões formais dos coeficientes verdadeiros.

## 5. Resultado matemático — ainda condicional

Não foram provados ainda em Lean os sinais `D₀..D₁₀>0, D₁₁<0` em `d=99/2000` nem `D₀..D₈>0, D₉<0` em `d=1/10`. Nenhum teorema final C5 incondicional existe nesta fase. O transporte C4 foi provado e auditado; O3/O4 permanecem abertas em `OPEN_OBLIGATIONS.md`.
