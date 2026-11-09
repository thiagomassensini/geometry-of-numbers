# C3/C6 — ponte condicional das caixas componentes ao primeiro determinante

`SigmaContour51FirstWindowComponentBridge.lean` conecta os registros componentes contínuos dos
4096 arcos à inclusão do integrando original em `n=0,1,2`. Os resultados geométricos de `s(u)` e
`z(u)` são aplicados diretamente em cada arco, e `contour51C5LogPiBox_contains` fornece `log π`.
Assim, os registros não repetem essas três inclusões previamente provadas.

## Hipóteses exatas

Para cada `k<4096`, `Contour51Arb4096FirstThreeArcComponentBoxes k` ainda exige:

- caixas contínuas por arco de `ζ(s)`, `ζ′(s)` e `digamma(s/2)`;
- `normSqRange` estritamente positivo para as caixas geométricas de `s`, para `s-1`, e para ζ;
- `normSqRange` estritamente positivo para `z^(2n+1)` para cada `n=0,1,2`;
- caixa intervalar composta com parte real inferior acima do endpoint Arb inferior e parte real
  superior abaixo do endpoint Arb superior, para cada `n=0,1,2`.

Os registros dos 4096 arcos implicam `contour51Arb4096FirstThreeArcEvaluatorInclusion`, que a
integração de partição uniforme transporta aos três intervalos de resíduos originais. A ponte
existente para o determinante mantém os cinco termos de
`D_s(H)-D_s(P)` e conclui o limite absoluto estrito
`1/1000000000 < CarrySigmaPade.sigmaPadeD 0 0`.

O teorema final não afirma a existência dos registros. A tabela externa Arb, seus endpoints e
margens racionais não provam as caixas contínuas nem as comparações com o avaliador Lean. Logo, a
margem central continua condicional.

## Compilação e auditoria

Lean 4.32.0, warnings como erros, saída exclusiva em
`/home/thlinux/tmp/c2-contour51-20261108-lean432`. Os três teoremas auditados dependem somente de
`[propext, Classical.choice, Quot.sound]`. O fonte não contém `sorry`, `admit` nem axiomas
declarados. Tentativa 1 falhou na projeção porque o teorema inferior existente também retorna uma
testemunha dos dez zeros; a tentativa 2 extrai explicitamente a desigualdade e compilou.

- Fonte SHA-256: `ab8fda175f859b0bdae99f1c4c55e12dd79f9ff06b14d63ce2333b11b6827c6c`.
- OLean SHA-256: `37aaf507c44b2960f2dfc2a1777f736fdc48a548272cdb3bdeb9c5d610391105`.
- Log SHA-256: `328ba1e8932550e8fb3918e51707b2f7e9eaa2b8878302754700cff08866afa0`.
- Log compilado: `C3_SigmaContour51FirstWindowComponentBridge-success.log`.
- Diagnóstico da tentativa 1: `C3_SigmaContour51FirstWindowComponentBridge-attempt1-failed.log`.
