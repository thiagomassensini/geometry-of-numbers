# Caudas quantitativas dos jets celulares e residual exato da PR #41

**Resultado: PARTIAL.** As caudas ordinária e logarítmica da fonte original
receberam cotas explícitas em toda ordem fixa. A estimativa foi transportada
até o residual algébrico exato da #41 e, separadamente, até os três termos
HT+TH+TT do Green reduzido. Não foi provado um novo sinal de pivô.
A aceleração TFVD finita também foi demonstrada, conservando os dois bordos;
a cota do seu resto infinito permanece aberta.

Base: `cfb407550c19f13d3f5525462bdd905db43f8378`, HEAD da PR #58,
branch `agent/material-green-summation-parts`.
Branch desta continuação: `agent/native-cell-jet-tail-bounds`.
É uma continuação empilhada, não uma branch que presume #38–#58 integradas
à main. `main`, PRs anteriores, dependências e fontes nativas foram preservados.
Não há merge automático.

## A — O que já estava demonstrado

1. A PR #41, commit `ee56930a2c30456cfbd214a29bb31b12d3977204`, fornece
   `NativeMomentOrthogonalization.momentFunctional`, `momentForm`,
   `orthogonalPolynomial`, `orthogonalPolynomial_self` e
   `momentForm_coefficients`. O residual é algébrico antes de ser uma norma.
   As identidades de auto-pareamento continuam válidas com divisões totais;
   a interpretação por inversa do bloco/ortogonalidade exige as condições
   de não anulação já explicitadas na #41.
2. A PR #54 fornece `CarryForcingResidual.criticalCoefficients` e
   `criticalPolynomial_exact`: usamos a mesma direção mônica, com os
   coeficientes originais, e não uma direção aproximada escolhida por sinal.
3. A PR #37 e seus consumidores identificam a resposta material completada
   e os jets do residual canônico. Reutilizamos
   `CarryMaterialThirdNullComparison.material_taylor_shift_center` e
   `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical`.
4. A PR #58 fornece `cell_jet_source`, `return_jet_head_tail`,
   `clock_return_jet_head_tail`, `reduced_return_tail_defect`, e a ligação do
   mesmo numerador Green ao residual canônico. Ela já cancelou o interior
   material sem apagar o retorno global. Essa prova não foi reconstruída.
5. `baseTwoSecondDifference_norm_le` limita a célula completa por sua segunda
   derivada. As curvas ℓ¹ analíticas e seus readouts originais também são
   preexistentes. Não postulamos domínios de potências do clock não limitado.
6. H6, K6 e as doze fontes são regressões preexistentes. Não entram como
   premissas nas novas cotas nem como origem dos momentos.

O índice material da cauda, a ordem do jet e a profundidade vertical
continuam distintos. A fonte é sempre n^(-1/2) exp(-it log n), com centro
4(k+1), pernas 4k+3 e 4k+5 e ambos os endereços de aresta.

## B — O que foi demonstrado agora

Todos os nomes abaixo pertencem ao namespace `CarryCellTail`.
Os arquivos Lean são a declaração precisa de hipóteses e convenções.

### 1. Célula completa e jets normalizados

`CellCauchy.lean`: `complex_cell_real`, `complex_cell_entire`,
`complex_cell_bound`, `complex_jet_bound`.
A continuação complexa é só uma ferramenta de estimativa da mesma célula:
para |w| ≤ 1/2,

    |cell_k(w)| ≤ 2/(4k+3)^2.

A prova toma a segunda diferença ANTES da norma. Utiliza z=-1/2-iw,
|z|≤1, |z-1|≤2 e Re(z-2)≤-2. Inclui z=0, sem dividir por esse expoente.
Cauchy, no raio 1/2, dá para o Taylor normalizado:

    |cellJet(m,k)| ≤ 2^(m+1)/(4k+3)^2.

`JetTails.lean`: `real_jet_complex`, `cell_jet_coefficient`,
`reciprocal_step`, `reciprocal_cell_tail`, `return_jet_quantitative`.
A passagem dos jets reais para os complexos é provada por germes e dslope;
o fator 1/m! é preservado. Uma envoltória telescópica racional soma TODOS
os termos omitidos. Para M≥1, com Q_M=4(4M-1),

    |jet_m beta - sum_{k<M} cellJet(m,k)| ≤ B(m,M)=2^(m+1)/Q_M.

Não é um resultado uniforme em m com constante independente da ordem.

`ClockTails.lean`: `clock_cell_real_derivative`, `complex_clock_real`,
`clock_jet_coefficient`, `clock_cell_jet_bound`,
`clock_return_jet_quantitative`.
O segundo canal conserva o multiplicador logarítmico da fonte e satisfaz

    clockCellJet(m,k) = i(m+1) cellJet(m+1,k),
    |jet_m kappa - sum_{k<M} clockCellJet(m,k)|
       ≤ K(m,M)=(m+1) 2^(m+2)/Q_M.

A primeira igualdade é formal, não um ajuste numérico de coeficientes.

### 2. Transporte ao readout canônico sem mudar o denominador

`NormalizedJets.lean` demonstra o produto de Taylor com todos os coeficientes
(`rJet_mul`), sua linearidade e o orçamento finito de convolução.

Em `ResponseTails.lean`, sejam D o dressing original e F a resposta completa.
Definimos somente os multiplicadores literais do readout já existente:

    A(t)=-D'(t)/(2F(t)),    B(t)=iD(t)/(2F(t)).

`original_response_center_ne` prova F(0)≠0 a partir do sinal completo e do
D original, sem positividade de Hankel. `normalized_response_channels` dá

    Q(t)=A(t)(1+beta(t))+B(t)kappa(t).

A observação finita Q_M usa os prefixos beta_M e kappa_M, mantendo **o mesmo
F no denominador e o mesmo D e D'**. Não é a derivada logarítmica de uma
característica truncada, nem uma nova sequência de momentos canônicos.
`response_tail_exact` conserva exatamente os dois canais:

    Q-Q_M = A (beta-beta_M) + B (kappa-kappa_M).

Para cada r, `response_jet_error` prova

    |jet_r Q-jet_r Q_M| ≤ E(r,M)
      = sum_{j=0}^r |jet_j A| B(r-j,M)
        + sum_{j=0}^r |jet_j B| K(r-j,M).

`native_moment_jet` identifica jet_(2n+1) Q com h_n original.
`native_moment_error` aplica E(2n+1,M) ao erro da observação de h_n.
Os jets de A e B permanecem constantes exatas do objeto completado original;
este trabalho não produziu intervalos executáveis para essas constantes.
Logo Q_M não é, por si só, um algoritmo fechado usando apenas M células.

### 3. O MESMO residual da #41, com todos os cruzamentos

`CriticalTail.lean`: `critical_pivot_coefficients`, `exact_critical_error`,
`critical_budget_rate`, `critical_cutoff_suffices`, `second_even_error`.
Se a_i são os coeficientes originais de P_(s,n), a observação é

    pObs(s,n,M) = sum_{i,j} a_i a_j hObs_M(i+j+s).

A prova usa literalmente `orthogonalPolynomial_self` e a expressão bilinear
com os dois índices independentes. Não usa o sinal de nenhum pivô.
Escrevendo E(r,M)=C_r/Q_M, obtemos

    |pivot(s,n)-pObs(s,n,M)| ≤ Ccrit(s,n)/Q_M,
    Ccrit = sum_{i,j} |a_i| |a_j| C_(2(i+j+s)+1).

A desigualdade vale também quando o pivot é nulo ou negativo; não o converte
num quadrado de norma. A leitura por complemento de Schur de uma matriz
invertível continua tendo as hipóteses originais da #41.

A regressão `second_even_error` particulariza a direção n=1, s=0 e recupera
exatamente h_2-h_1²/h_0, sem receber sua positividade como hipótese.
Um cutoff é suficiente para erro ε se Ccrit≤ε Q_M.
Este é um teste explícito de precisão, não uma prova de que um cutoff
pequeno já satisfaz a condição e não uma hipótese de positividade renomeada.

### 4. HT, TH e TT do próprio Green

`GreenTailBounds.lean`: `ordinary_tail_point_bound`, `clock_tail_point_bound`,
`native_tail_pair_exact`, `native_tail_pair_bound`, `full_green_tail_budget`.
Aqui os parâmetros são reais, |t|,|u|≤1/4, e M,L≥1 são independentes.
Se T_M é o par de cauda original, a identidade exata é

    T_M(t)=(iD(t) kappaTail_M(t)-D'(t) betaTail_M(t),
            D(t) betaTail_M(t)).

Uma magnitude de ERRO e(t,M)=(10|D(t)|+2|D'(t)|)/Q_M limita
|T_M,1|+|T_M,2|. Isso não é uma nova métrica física.
Com H_M o par de prefixo, l(x)=|x_1|+|x_2| e

    k(t,u)=|a²tu|+|a(u-t)|/2,    a=h_0 original,

`full_green_tail_budget` limita o defeito reduzido original por

    k(t,u) [ l(H_M(t)) e(u,L)
             + e(t,M) l(H_L(u)) + e(t,M)e(u,L) ].

Os três termos correspondem a HT, TH e TT da identidade exata da #58.
O termo assinado do companheiro, D', os fatores e os dois argumentos foram
conservados antes de tomar módulos. A cota é pontual para o NUMERADOR;
não se divide por tu(u-t) perto do centro para inferir uma cota de jets.
O transporte ao residual crítico na seção anterior tem sua própria prova
por jets do readout canônico, com denominador completo fixo.
Não identificamos as duas aproximações finitas como se fossem o mesmo kernel.

### 5. Aceleração TFVD exata, com os bordos visíveis

`TailAcceleration.lean`: `tail_acceleration_cell`, `tail_acceleration_finite`,
`native_cell_delta2`, `native_tail_window_acceleration`.
Para qualquer sequência complexa f, sejam

    Bf(a)=[3f(a+2)-8f(a+1)+5f(a)]/8,
    Rf(a)=3/8 Delta^4 f(a)+1/2 Delta^4 f(a+1)+3/8 Delta^4 f(a+2).

O Lean prova, sem hipóteses de sinal ou convergência,

    sum_{k<N} Delta² f(a+4k)
       = Bf(a)-Bf(a+4N)+sum_{k<N} Rf(a+4k).

A especialização nativa usa a=4M+3 e a MESMA f_t(n)=n^(-1/2)exp(-it log n).
É uma identidade finita de aceleração, não um novo peso da fonte.
Nenhum bordo foi apagado. A versão infinita e sua cota acelerada não foram
reivindicadas: exigem decaimento do segundo bordo e controle do resto.

## C — O que foi refutado ou não pode ser concluído

- As cotas não orientam o sinal do residual. Os controles racionais testam
  pivôs -1, 0 e 1 e passam nos três casos.
- A cota bruta é conservadora. Para o jet ordinário m=5, o critério B≤10^-8
  exige M=400000001; para B≤10^-25 exige
  M=40000000000000000000000001. São custos desta envoltória de UM JET,
  não cutoffs ótimos nem orçamentos completos do pivô. Nenhuma dessas
  campanhas foi executada.
- Isso não é um no-go da fonte nem da precisão por células. É motivo para
  conservar cancelamentos e estimar o resto de quarta diferença já isolado.
- Uma cota em módulo, uma identidade algébrica de ortogonalização, uma
  aproximação finita ou a validade da aceleração finita não demonstra Gram
  positiva global, contratividade all-order ou espectro positivo.
- Não foi obtida uma lei de sinal em toda ordem, nem uma identificação nova
  do clock material bruto com os momentos canônicos.

Nos testes da mesma fonte, sem theta, zeros ou alturas como entradas, a
janela M=16, N=128 no jet m=5 deu módulo 0,00303115697458 para a soma
original e 0,000000912585313 para o resto de quartas diferenças. A identidade
conserva os dois bordos também nesse teste. É evidência NUMÉRICA FINITA de
que a aceleração merece a próxima cota; não é uma estimativa do resto
infinito nem um sinal de pivô. Os valores completos estão em
`evidence/experiment.json`.

## D — O que está no kernel e o que permanece aberto

Os oito módulos matemáticos contêm 63 teoremas e 27 definições, inventariados
em `public-roots.json`. São provas
Lean 4. `Audit.lean` imprime axiomas e percorre transitivamente TIPOS E CORPOS.
Os guards rejeitam certificados H6/K6/H7 e consumidores de positividade
all-order; as fundações permitidas são somente propext, Classical.choice e
Quot.sound. As auditorias Foundation/Geometry/Analysis permanecem separadas.
Os controles `experiment.py` são regressões, não certificados de sinal.

**Validação completa: 19/19 verificações com código de saída zero.** Os nove
módulos (oito matemáticos e Audit) foram compilados explicitamente com
warningAsError. Passaram os builds focado e raiz com `lake build --wfail`,
as auditorias Foundation/Geometry/Analysis, os controles exatos e numéricos,
a regressão das doze fontes, a preservação dos arquivos históricos e o
`git diff --check`.

A auditoria das 90 raízes públicas percorreu estes tamanhos de fechamento
transitivo (tipos e corpos): células 3679; clock 3737; cálculo 3112;
resposta 5412; crítico 5460; bordo 5717; aceleração 1653. Somente os três
axiomas fundacionais permitidos foram encontrados. Nenhum novo axioma
matemático ou admissão foi introduzido.

A checagem de preservação confirmou main e origin/main em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, a branch #58 em sua base acima,
as demais refs protegidas, pins, worktrees e os arquivos preexistentes do
operador e da #51. Nenhuma worktree foi criada ou removida.

Reprodução, no host llm, sem instalar dependências ou alterar pins:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/native-cell-jet-tail-bounds/validate.py
```

A reprodução indicada reutiliza o ambiente e os caches Lean já preparados
pela #58 no host llm; os caminhos estão explícitos em `compile_module.sh`.
Em um checkout novo, preparar antes as dependências de pesquisa conforme
os relatórios das PRs ancestrais. O script compila explicitamente todos os
módulos desta continuação com warningAsError,
executa `lake build --wfail`, auditorias e regressão das doze fontes.
A regressão numérica usa o Python 3.12 existente em
`/home/thlinux/miniforge3/bin/python3`, com mpmath 1.3.0; os testes racionais
usam Fraction. `evidence/checks.json` registra comandos e saídas; o manifesto
SHA-256 distingue fontes e logs. Não foram alteradas dependências.

Permanece aberto o sinal independente do residual canônico. Não há aqui
prova de positividade da Hankel original em toda ordem nem construção de
uma Gram substituta.

## E — Próximo passo mínimo

Não repetir a extração forte dos jets nem a prova de convergência qualitativa.
A cota explícita de erro da direção #41 já existe agora. O trabalho mais
curto com chance de tornar a avaliação econômica é:

1. Estimar a QUARTA diferença da mesma continuação material no círculo
   complexo e transportar a estimativa aos jets normalizados. Um candidato
   concreto a provar é |Delta^4 f_m(a)|≤24*2^m/a^4 para a≥1, usando a mesma
   circunferência de raio 1/2. Esta desigualdade NÃO é resultado deste PR.
2. Provar o desaparecimento do bordo Bf_m(a+4N) e somar o resto controlado
   da identidade já demonstrada. Isso testará uma taxa cúbica em M, sem
   substituir a fonte. Nenhum ganho assintótico é anunciado antes disso.
3. Na direção segunda par, certificar intervalos dos coeficientes finitos
   de A,B (ou controlar a mesma divisão por um esquema intervalar provado)
   e da observação. Só então verificar uma desigualdade de margem completa:
   pObs > orçamento de erro, sem inserir o pivô positivo como entrada.

Mesmo uma nova margem finita não demonstrará a lei all-order. Para isso
segue faltando uma propriedade independente do transporte/fonte que
restrinja o sinal do mesmo residual, além do seu controle de aproximação.
