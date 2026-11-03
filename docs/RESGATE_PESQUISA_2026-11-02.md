# Resgate e cartório das branches de pesquisa — 02/11/2026

Este documento é um **mapa de proveniência**, não uma prova matemática nem uma declaração de que todos os arquivos `research/` são compilados no CI principal. Sempre leia a declaração Lean original, sua auditoria e o contexto do certificado.

## Situação da integração

Após integrar a cadeia #134–#146 (main `9d6ca497dd8d3d5eba9839ebf362accd049a5297`), foi realizada uma varredura comparativa de **124 branches remotas preexistentes** em `thiagomassensini/geometry-of-numbers`. Nenhuma branch original foi apagada, renomeada ou rebased. Divergência de commits não foi interpretada como diferença de arquivos: listas `compare main...branch` representam mudanças a partir de um ancestral comum; a presença efetiva foi confirmada na árvore de `main` e nos diffs das PRs novas.

Três linhas de pesquisa que não estavam na árvore do `main` foram recuperadas por PRs pequenas, preservando os **blobs originais**:

| PR | Origem histórica | Material agora na main | Alcance |
| --- | --- | --- | --- |
| [#147](https://github.com/thiagomassensini/geometry-of-numbers/pull/147) | [`canonical-native-boundary-transfer`](https://github.com/thiagomassensini/geometry-of-numbers/tree/canonical-native-boundary-transfer) (`1c7d439ba520bb89187e1c66c4792ba856851b97`) | `research/canonical-native-boundary-transfer/CanonicalNativeBoundaryTransfer.lean` e `REPORT_PRELIMINARY.md` | Log-derivative moment sequence e sinal da ordem zero; **não** positividade em toda ordem |
| [#148](https://github.com/thiagomassensini/geometry-of-numbers/pull/148) | [`capstone-canonical-native-boundary-positivity`](https://github.com/thiagomassensini/geometry-of-numbers/tree/capstone-canonical-native-boundary-positivity) (`190ea84e64266ee39711300ee6f39d8319465791`) | `research/canonical-native-boundary-transfer/{CanonicalBoundaryTransfer.lean,Audit.lean,compile_module.sh,REPORT.md}` | Transporte H_n/K_n → energia de bordo nativa; **E8 e E12 finitos** via H6/K6 |
| [#149](https://github.com/thiagomassensini/geometry-of-numbers/pull/149) | [`k7-odd-canonical-source`](https://github.com/thiagomassensini/geometry-of-numbers/tree/k7-odd-canonical-source) (`d65787fc49bbc4da52c400b40b65d76c1db5faba`) | `research/seventh-odd-canonical-source/{K7PivotBridge.lean,K7ThetaBounds.lean,Audit.lean,REPORT.md}` | Equivalência do sinal K7 a porta theta/Schur, reutilização T26 e extensão tabulada T28; **não** demonstra sinal positivo de K7 |

O relatório preliminar da #147 foi renomeado para `REPORT_PRELIMINARY.md` para coexistir com o relatório posterior do capstone. O conteúdo de ambos os relatórios é mantido sem alterações.

## Hashes dos dez blobs preservados

Os valores abaixo são Git **blob SHA**, não hashes de arquivos renomeados ou de commits:

```text
research/canonical-native-boundary-transfer/CanonicalNativeBoundaryTransfer.lean  9ee4ccef79bf5885122570c413fe58df6d5e1371
research/canonical-native-boundary-transfer/REPORT_PRELIMINARY.md          9fa37e8eaa074d1d1df78cdbc0df67175f54a410
research/canonical-native-boundary-transfer/CanonicalBoundaryTransfer.lean 94be9775c96613370a1c3f8279adcaa22afa681a
research/canonical-native-boundary-transfer/Audit.lean                     3de682949b8e662c7ef07058aaec2bc9d9a23c66
research/canonical-native-boundary-transfer/compile_module.sh             7e020e2f5ca07a03ae4016445c0368166acc42d3
research/canonical-native-boundary-transfer/REPORT.md                     6b8ec23d41aad2f870f7734b00f77c8b1029e824
research/seventh-odd-canonical-source/K7PivotBridge.lean                  d3837cf1c811d3971b6b66fb05abe601754268b6
research/seventh-odd-canonical-source/K7ThetaBounds.lean                  ea6197f964d1721164f4e99150fce6a32aa91aa5
research/seventh-odd-canonical-source/Audit.lean                          eb01c29e8038d88b396d5be992d4dbac538c5d61
research/seventh-odd-canonical-source/REPORT.md                          d695c767b8e538352dc2cb1a6497dd1c015d3e97
```

## Pesquisa que já estava preservada: o retorno físico

A branch antiga `agent/native-positive-square-kernel` inclui `research/native-return-boundary-deflation/` e a [PR #52](https://github.com/thiagomassensini/geometry-of-numbers/pull/52) registra sua integração histórica. Esse diretório, inclusive dados, scripts e auditorias, **já está na main** com o mesmo Git subtree SHA `9dbf987f5375d527bc7d1abf8ad98ae8c9cdfe41`. Uma tentativa de resgate em [#150](https://github.com/thiagomassensini/geometry-of-numbers/pull/150) produziu **zero arquivos alterados** e foi encerrada **sem merge**. Não há motivo para duplicar essa árvore.

A pesquisa de retorno físico identifica uma decomposição vetorial com reconstrução do estado original e um canal positivo eventual, mas seu residual é **assinado**. Na direção ortogonal da PR #41 a parcela positiva extraída tende a zero e o residual retém o primeiro Schur canônico. **Não** é prova de positividade geral. Leia [o relatório](../research/native-return-boundary-deflation/REPORT.md).

## Limites de validação

- Os capstones E8/E12 e K7 possuem registros históricos de compilação dirigida e auditoria, geralmente reutilizando caches e módulos `.olean` do operador; os resgates **não repetiram** essas compilações em clone limpo.
- O workflow [`lean-main.yml`](../.github/workflows/lean-main.yml) é acionado por `push` na main, e verifica `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. Ele **não** compila automaticamente todos os módulos em `research/`. Um CI verde não certifica, sozinho, a reprodutibilidade desses módulos.
- Nenhum resultado foi reescrito como all-order. Dependências específicas e proveniência de caixas theta devem continuar explicitadas. Não se deve inferir que a positividade da sequência auxiliar do material clock é igual à da sequência canônica completada.
- Auditoria Git de histórico: branches com `ahead_by > 0` e listas de arquivos vazias não foram mergeadas só para alterar o histórico. Para uma verificação futura, prefira **comparar árvores efetivas** (por exemplo, `git diff main <branch> -- research/`) antes de declarar um arquivo ausente.
- Nenhuma branch, arquivo local não rastreado, checkout do operador ou pin foi removido ou alterado nesta missão.

## Obrigações matemáticas ainda abertas

1. **K7 ímpar:** obter uma caixa rigorosa e suficientemente estreita para T28 e uma margem correlacionada do Schur, sem perder precisão em um prefixo numericamente mal condicionado.
2. **C3 terceira direção:** certificar `c4` para o prefixo ímpar a partir da fonte completa, com cabeça, cauda e cruzamentos; depois controlar `c5` e `c6` para os pivôs novos.
3. **Green/TFVD e polarização completa:** a identidade de quatro canais e a extração positiva isolada não fornecem, por si, sinal positivo para o residual ou para os pivôs de Schur em toda ordem.
4. **Reprodutibilidade:** em etapa independente, validar os resgates por compilação Lean focada no estado atual das dependências e, se apropriado, acrescentar CI isolado que respeite os caches/pins sem mexer nos enunciados.

**Política de preservação:** manter ramos originais intactos; carregar declarações com status exato (proved, conditional, experimental, NO-GO); preferir PRs pequenas com nomes de prova e relatórios originais.
