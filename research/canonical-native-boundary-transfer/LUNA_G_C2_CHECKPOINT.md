# Luna G — certificação finita do sinal C2

## Bases e cadeia entre repositórios

Este resultado é downstream do PR #118 do repositório
`carry-self-adjoint-operator`:

- branch principal: `codex/luna-g-c2-energy-limit-2026-11-14`;
- commit de transporte: `a90e84a`;
- base dessa branch: head #117, `87e448a6c2fdd35b61cc3f6ff824bef9dc1b4b88`.

O trabalho de certificação está isolado na branch deste repositório
`codex/luna-g-c2-sign-transport-2026-11-14`, baseada em
`ca621765d4a4c1c1254a7df282d95926f29d362f` (`main`, após #330). A direção
dos imports é Geometry of Numbers → self-adjoint; o repositório principal não
importa módulos Geometry of Numbers, então a cadeia não cria ciclo.

## Certificados usados e restrição de ordem

Os PRs #148, #323, #327 e #329 já estão integrados em `main` e fornecem o par
canônico H6/K6 estritamente positivo a partir de certificados finitos da
fonte. A transferência em #148 já prova E12 diretamente e E8 pela seção
principal de ordem 4.

Este complemento formaliza em Lean a restrição do par H6/K6 por
`Fin.castLE_injective` para todo `n ≤ 6`. O resultado é
`canonical_hankel_pair_posDef_of_le_six`. A divisão par/ímpar da energia
original então dá
`nativeSourceFiniteBoundaryEnergy_pos_2n_of_le_six`: para cada `n ≤ 6`, a
energia nativa em dimensão `2*n` é estritamente positiva em todo vetor não
nulo. Portanto, as ordens-alvo `1 ≤ n ≤ 6` incluem as dimensões 2, 4, 6, 8,
10 e 12. E8 e E12 também permanecem identificados por seus teoremas
específicos já existentes.

## Transporte C2 certificado

`nativeSourceC2CentralLeg_eventually_positive_of_order_le_six` combina a
positividade acima com
`nativeSourceC2CentralLeg_eventually_margin_of_boundary_pos`, do PR #118.
Para cada ordem fixa `n ≤ 6`, Lean fornece um `δ_n > 0` tal que, eventualmente
em `k` radial,

```text
δ_n * ‖x‖² ≤ nativeSourceC2CentralLegReadout n k
  (nativeSourceC2TailCutoff n k) x
```

O `δ_n` é obtido por compacidade em dimensão finita e pode depender de `n`;
não se afirma valor numérico nem uniformidade nas ordens. O corte continua
sendo exatamente `M(n,k) = nativeSourceC2TailCutoff n k`, escolhido no PR #117
com orçamento da cauda `1/(k+1)`. `n` é ordem de Hankel, `k` é índice radial
e `M` é o número de células C2 incluídas. Não há identificação entre esses
índices nem troca de limites.

## Hipóteses e fronteiras

- O sinal de `Q` nas ordens 1–6 está provado usando somente certificados
  finitos H6/K6 e o transporte quantitativo do PR #118.
- Nenhuma positividade Hankel de ordem arbitrária é afirmada. A hipótese
  `InfinitePositiveRealNativeZeros` continua explícita nos consumidores
  estritos de positividade geral; ela não é usada para esta certificação
  finita.
- A estimativa geral para ordens `n ≥ 7` permanece aberta; o sinal de centro
  + pernas de E4 não foi presumido nem deduzido além das seis ordens.
- O transporte C2 está no PR #118 do repositório principal; sua instanciação
  com H6/K6 fica neste PR downstream para respeitar o grafo de imports.

## Verificação

Compilação e audit usam o script já existente com o checkout da branch #118
passado como segundo argumento:

```text
bash research/canonical-native-boundary-transfer/compile_module.sh --check \
  CanonicalBoundaryTransfer /home/thlinux/worktrees/luna-g-c2-energy-20261114
bash research/canonical-native-boundary-transfer/compile_module.sh \
  CanonicalBoundaryTransfer /home/thlinux/worktrees/luna-g-c2-energy-20261114
bash research/canonical-native-boundary-transfer/compile_module.sh \
  Audit /home/thlinux/worktrees/luna-g-c2-energy-20261114
```

As três etapas passaram. A compilação usa `-DwarningAsError=true`. A auditoria
transitiva das raízes genéricas, E8/E12 e do novo sinal C2 reporta somente
`propext`, `Classical.choice` e `Quot.sound`. Nenhum `sorry`, `admit` ou novo
axioma foi adicionado.
