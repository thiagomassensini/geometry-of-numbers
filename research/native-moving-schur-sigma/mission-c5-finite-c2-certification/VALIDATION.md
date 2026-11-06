# C5 — validação

**Status atual:** Fase 1 de transporte algébrico integrada pela PR #165. O3 (propagação racional Lean e sinais condicionais) foi integrada pela PR #167, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. O checkpoint O4 foi integrado pela PR #169; estados pós-merge pelas PRs #170, #172 e #174; pontes Euler-Gamma pelas PRs #171, #173 e #175. A prova `gamma_finite_3072_620_error` tem erro `≤10⁻²⁵⁹`, build Lean 4.32 e auditoria de doze raízes. O4 continua aberta: a expressão finita e as inclusões da fonte ainda precisam de caixas certificadas.
**Toolchain:** `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
**Base geometry da PR #165:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776`; `main` após o merge: `75691edf0e74cc643f098213f60b684476132175`.
**Fonte C4 compilada:** source hashes de `SigmaSourceBezout.lean`, `SourceBezout.lean`, `SigmaPadeCorrespondence.lean` e `SigmaZeroObstruction.lean` conferem com `origin/main`; pins completos em `evidence/pins-and-sha256.txt`.

**O4, auditoria de 2026-11-06:** os módulos de intervalo elementar foram recompilados e auditados; também foi localizada a identidade formal de Weierstrass `Zeta23.DigammaSeries.inv_gamma_eq_prod`. Nenhuma caixa numérica para `Complex.Gamma` foi ainda derivada dessa identidade, e a aproximação Stirling usada pelo avaliador segue sem ponte Lean. O4 e a inclusão incondicional das caixas continuam abertas.

**O4, prova Euler-Gamma de precisão alta integrada pela PR #173:** `gamma_finite_1024_240_error` aproxima a Gamma original por `gammaFinite 1024 240 z` com erro `≤10⁻⁹⁹` para `1495/20000≤Re(z)≤1`. Build Lean 4.32 e auditoria de dez raízes passaram; a caixa racional estreita da expressão finita continua pendente. Prova, logs e hashes estão em `evidence/rational-boxes/`.

## 1. Transporte algébrico Lean — PASSOU

Arquivos novos:

- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean`
- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransportAudit.lean`

A prova começa em `completedSigmaDisplacedSource_coefficient_recurrence` de C4 e mantém `completedSigmaDisplacedMoment = 2*completedSigmaLogJet`. O módulo prova a recorrência polinomial sem divisão, a identidade do menor escalado com `CarrySigmaPade.sigmaPadeD` original e os dois lemas de transferência de sinal usando `completedSigmaDisplacedSourceCoefficient_zero_pos`.

O build final foi feito para diretório de saída novo, com warnings tratados como erros, usando o script `compile_sigma_pade.sh`. Os logs e o comando exato estão em `build-transport-clean.log` e `transport-build-record.md`.

`#print axioms` para os quatro teoremas auditados lista apenas `propext`, `Classical.choice` e `Quot.sound`. Saída em `axiom-audit-transport-clean.log`. Nenhum axioma próprio, `sorryAx` ou `admit` foi introduzido.

PR #165 foi integrada à `main`; o GitHub não retornou status checks hospedados. A validação local registrada acima é o resultado de build/auditoria desta fase.

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

## 5. Sinais condicionais — provados em Lean

O3 compõe as caixas racionais com a recorrência polinomial sem divisão e prova
em Lean os sinais condicionais dos menores. Os teoremas
`sigmaPadeD_signs_at_99_2000_of_source_boxes` e
`sigmaPadeD_signs_at_1_10_of_source_boxes` concluem sobre o `sigmaPadeD`
original, assumindo respectivamente `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`. Todos os índices requeridos foram cobertos: `D₀..D₁₀>0,
D₁₁<0` em `d=99/2000` e `D₀..D₈>0, D₉<0` em `d=1/10`.

O build limpo dos seis módulos e a auditoria das 13 raízes passaram; apenas
`propext`, `Classical.choice` e `Quot.sound` aparecem. Consulte
`evidence/rational-boxes/VALIDATION.md` para comandos, logs e hashes.

## 6. Resultado incondicional — ainda aberto

Os dois teoremas finais de primeira janela negativa ainda não são
incondicionais, pois O4 não prova que os coeficientes reais da fonte C2 original
estão dentro das caixas. A fonte permanece a cabeça C2, a cauda exponencial
exata e a completação original; os resultados condicionais não substituem essa
prova. A primeira obrigação aberta está em `OPEN_OBLIGATIONS.md`.
