# C5 — certificado do prefixo 0–32 da tabela de Bernoulli

## Resultado

`c5BernoulliPrimeTable_32_eq_data` prova que as primeiras 32 entradas da tabela
recursiva de Bernoulli usada na avaliação intervalar coincidem com o prefixo
literal `c5BernoulliPrimeDataPrefix32`. Isso inicia a decomposição por blocos
para certificar, sem reexpandir a tabela recursiva em cada caixa de zeta, os
601 coeficientes usados pela correção Euler–Maclaurin.

O dado completo de 601 entradas vem da avaliação Lean de
`c5BernoulliPrimeTable 601`; os prefixos estão separados em blocos de 32 em
`SigmaC5BernoulliDataTable.lean`. Só o primeiro bloco está provado neste
checkpoint. Nenhuma caixa exportada de zeta, inclusão de fonte ou sinal C5 é
certificado por esta etapa isolada.

## Build e auditoria

- Lean 4.32.0; `warningAsError=true`.
- `SigmaC5BernoulliDataCertificate.lean` compila em 2:34, com pico de RSS de
  aproximadamente 3.7 GiB.
- A reprodução limpa repete a sonda Lean e confere, por comparação racional
  exata, que os 601 valores da tabela literal coincidem com a saída da
  recorrência executada.
- A auditoria isolada e o `#print axioms` do próprio módulo mostram somente
  `propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx`, axiomas
  próprios ou `native_decide`.
- A tabela literal compila em aproximadamente 12 segundos. A sonda que gerou
  os 601 valores levou 1:42 e atingiu 2.7 GiB de RSS.
- Pins: Lean `leanprover/lean4:v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

Reprodução limpa: `bash .../reproduce-clean.sh`. Os logs individuais e hashes
são gravados nesta pasta.

## Tentativa longa preservada

Antes de dividir o trabalho, tentei provar a igualdade da tabela inteira em
uma única indução. A fonte gerada com 601 valores e todos os 601 casos ficou
em compilação por 28:32; a execução foi interrompida sem produzir o teorema.
Pico observado: 4.6 GiB. O log está em
`attempts/full-table-monolithic-proof.log`. A primeira prova do prefixo 32 que
expandia a constante inteira em cada caso também foi interrompida após cerca de
5:49; o registro dessa tentativa está em
`attempts/prefix32-full-table-expansion.md`. Isso motivou separar os prefixos
em blocos antes de certificar o primeiro.

## Próximo passo

Provar o prefixo 32–64 usando o resultado deste bloco como base, e continuar
com blocos de 32 até obter `c5BernoulliPrimeTable 601 =
c5BernoulliPrimeData601`. Só então testar novamente a ponte exata de um nó
entre a caixa centrada de zeta e seus extremos exportados.
