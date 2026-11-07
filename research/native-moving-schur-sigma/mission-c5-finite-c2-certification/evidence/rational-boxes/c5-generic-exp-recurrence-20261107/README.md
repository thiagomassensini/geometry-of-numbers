# C5 — recorrência genérica da exponencial arredondada

**Estado:** checkpoint validado localmente, ainda não publicado pela PR deste
subpasso. C5 permanece incompleta: ainda faltam a ponte CSV–Lean, a inclusão
dos coeficientes da fonte C2 nas caixas e os sinais condicionais finais.

## Resultado validado

`SigmaC5ZeroExpGenericRecurrence.lean` prova uma fórmula única para todos os
estágios `2 ≤ k ≤ 192` na entrada nula. Definindo `r = k - 2`, a caixa é

```text
c5GenericBox (3 * 2^r - 1) (4 * 2^r - 1).
```

A prova deriva as desigualdades exatas dos quatro extremos da caixa quadrada,
certifica os pisos e tetos em 896 bits e obtém a atualização dos parâmetros
`a ↦ 2a+1`, `b ↦ 2b+1`. O estágio base usa a identidade já certificada
`c5ZeroExpStage2_eq`. Para `r ≤ 190`, os limites `a,b < 2^192` e
`2*b^2 < 2^896` garantem que a mesma demonstração vale em cada passo. A
conclusão fala diretamente sobre `c5RoundedExpC` original e mantém a inflação
racional explícita do resto de Taylor definida por esse operador.

O build limpo passou com Lean 4.32.0 e `warningAsError=true`. A auditoria
separada não encontrou axiomas além de `propext`, `Classical.choice` e
`Quot.sound` nos quatro teoremas listados. Os logs e cópias exatas das fontes
estão nesta pasta. Os hashes das fontes, auditorias e `.olean`s locais estão
em `stage-sha256.txt`.

## Pins e reprodução

Os pins, a revisão-base da `main`, as fontes e os diretórios de cache de
dependências estão em [`pins.txt`](pins.txt). O script
[`reproduce.sh`](reproduce.sh) recompila primeiro o módulo-base de estágios,
depois a recorrência e sua auditoria. Ele grava a saída em
`research/native-moving-schur-sigma/.cache/c5-generic-exp-recurrence-20261107/logs/`.

Da raiz do checkout Geometry:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-generic-exp-recurrence-20261107/reproduce.sh
```

O build ocorreu com cerca de 60,5 GiB de memória disponível, acima do portão
de 30 GiB do script de compilação.

## Erros de ambiente encontrados e resolução

A primeira tentativa usou um `SigmaC5ZeroExpStagesCertificate.olean` antigo,
que não expunha `c5ZeroExpStage2_eq`; a compilação então parou com identificador
desconhecido. O módulo-base foi recompilado a partir da fonte para o diretório
de saída da reprodução. Outra tentativa procurou uma dependência em um cache
incompleto de validação C3 e falhou por ausência do objeto
`Mathlib.NumberTheory.ZetaValues`. Os dois logs foram preservados em
`attempts/`. O script de reprodução limita a busca aos caches de módulos
diretamente usados. Não há erro de compilação pendente na versão validada.

## Escopo restante

Este teorema só certifica a recorrência na entrada zero. Ele não conecta as
516 caixas CSV às definições Lean, não prova
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` e não fecha os sinais C5. A
próxima etapa continua sendo a ponte CSV–Lean e a composição da fonte original.

