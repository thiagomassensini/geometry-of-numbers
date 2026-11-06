# C5 — obrigações abertas

## O1 — validar o cálculo racional já publicado

Executar `verify_signs_exact.py` para os dois JSONs de Momentos. Conferir que os arquivos
contêm extremos racionais exatos e que os sinais calculados são `+++++++++++-` e `+++++++++-`.
Isso só valida a implicação condicional às caixas.

## O2 — transporte C4 em Lean

Usar `C_d·H_d=-C_d′`, onde `H_d(n)=2*completedSigmaLogJet d n`, para provar a recorrência de
`p_n=c_0^(n+1)H_d(n)` e a identidade do determinante com o fator `4*c₀^(2s+4)`. Não introduzir
divisões na recorrência nem redefinir os momentos.

## O3 — aritmética intervalar racional formal

Portar as duas caixas a intervalos racionais e formalizar a recorrência dos `p_n`, a inclusão
dos polinômios dos determinantes e a exclusão de zero para todos os índices solicitados.
Float não pode decidir sinal.

## O4 — fonte das caixas

Provar inclusões rigorosas dos coeficientes `c₀..c₁₄` em `d=99/2000` e `c₀..c₁₂` em `d=1/10`,
preservando cabeça C2 + cauda geométrica exata + completação original. Certificar restos de
Hurwitz/Euler–Maclaurin, Stirling, operações elementares, contorno Cauchy/Fourier e todos os
domínios usados. A saída Python atual não fecha essa obrigação.

## O5 — composição, build, axiomas e publicação

Só chamar as conclusões de incondicionais quando O4 for fechado. Compilar em Lean 4.32, auditar
axiomas próprios/`sorryAx`, registrar logs e hashes, publicar checkpoints pequenos e verificar
PR/merge/main conforme a regra da missão.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependam das caixas explicitamente condicionais e relatar precisamente
qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar
`PROVADO — CERTIFICAÇÃO COMPLETA`.
