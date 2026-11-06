# C3: direções negativas nos setores par e ímpar

**Status:** prova e validação Lean 4.32 concluídas; integração na `main` pendente desta PR.

## Resultado

`exists_even_sigma_negative_directions_from_pade` e
`exists_odd_sigma_negative_directions_from_pade` partem do corolário C2 integrado,
`exists_eventually_negative_sigmaPadeD_from_height50_certificate`. Para o limiar `i₀`
fornecido por C2:

- o índice `p = 2 * i₀` dá uma janela negativa em `sigmaMatrix (1/5) 0 (i₀ + 2)`;
- o índice `p = 2 * i₀ + 1` dá uma janela negativa em `sigmaMatrix (1/5) 1 (i₀ + 2)`;
- em cada setor, o lema de persistência de C1B transporta essa direção a toda dimensão
  `M ≥ i₀ + 2`.

Os resultados exibem um vetor real não nulo cuja forma quadrática é negativa em cada
dimensão dessas duas torres. A prova usa os menores Padé originais e a matriz construída
com `completedSigmaLogJet` original. C2 continua a conservar a decomposição completa do
resto exponencial, sem hipóteses adicionais de sinal.

## Validação

- Lean 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame
  `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` e Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- O build externo da altura 50 compila com `warnings-as-errors`; os relatórios aceitos
  contêm somente `propext`, `Classical.choice` e `Quot.sound`.
- O build da integração C2 e seu checker aceitam os 17 relatórios de axiomas.
- O build focado C3 e seu checker aceitam os quatro relatórios registrados neste diretório.
- A auditoria transitiva percorre 133 raízes públicas e 70.861 dependências de tipos/corpos;
  mantém a característica e os jets sigma originais na proveniência e aceita somente os
  axiomas padrão.
- `git diff --check`, sintaxe dos scripts e os três checkers de axiomas passaram antes da
  publicação. Os logs integrais são preservados byte a byte com gzip: build externo em
  `height50-full-build.log.gz`, rebuild C2/C3 em `c2-c3-clean-build.log.gz` e fechamento
  de source closure em `c2-source-closure-build.log.gz`. O rebuild C1/C1B está em
  `c1b-clean-rebuild.log`; os resultados dos checkers estão nos arquivos `*-axiom-audit.log`;
  a auditoria transitiva está em `c2-c3-transitive-audit.log`. Hashes de fonte e pins estão
  em `source-sha256.txt`.

O root C2 integrado continua usando a composição exigida: `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`. A conclusão permanece em `completedSigmaLogJet`/`sigmaPadeD`; a decomposição conserva o resto exponencial e nenhum pressuposto de sinal foi acrescentado.

## Correção mínima da closure Lean 4.32

Uma recompilação limpa de C2 identificou que a closure local omitia
`SigmaTransverseAllOrder.lean` e `SigmaTransverseJoint.lean`, apesar de ambos serem
importados pela integração já publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
Os dois fontes foram restaurados byte a byte dessa revisão e compilam antes de
`SigmaZeroPairDecomposition.lean`.

Na closure reunida, há uma única declaração `def sigmaLineZero`, em
`SigmaCertifiedNegativeDirection.lean`; `SigmaRHHeightBridge.lean` a reutiliza.

O primeiro build externo dessa recompilação também revelou que o pacote certificado
vendorizado não continha `hunts/rh_height_lean/lean/CheckMain.lean`. O arquivo foi
restaurado da mesma revisão 4.32; seu SHA-256 confere com o arquivo em `b9ce195` e o build
completo subsequente compila `RHHeight.Main` antes de executar `CheckMain.lean` e seu
checker de axiomas. A saída completa está em `height50-full-build.log.gz`.
Esses reparos fecham somente a closure necessária para reproduzir a rota 4.32. Não houve
migração geral de Geometry ou Carry. A tentativa separada 4.35 permanece arquivada como
validação incompleta em `evidence/lean435-validation-incomplete/`.

## Reprodução

Com os checkouts nos pins acima e pelo menos 30 GiB de memória disponível:

```bash
CARRY_LEAN_ROOT=/path/to/carry-at-045369 \
SIGMA_REFERENCE_ROOT=/path/to/geometry-c1-checkout \
bash research/native-moving-schur-sigma/build_height50_sigma.sh /absolute/path/to/output
```

O runner reconstrói a closure externa e C1/C2, compila os dois resultados C3, valida os
17 relatórios de integração e roda a auditoria transitiva de Padé. Os logs versionados
neste diretório são a evidência desta execução.
