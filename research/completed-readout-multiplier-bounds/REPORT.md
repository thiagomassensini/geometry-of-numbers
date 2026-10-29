# Multiplicadores do readout completado: cotas racionais e residual da PR #41

**Resultado: PARTIAL.** O gate das cotas superiores dos multiplicadores da
PR #60 foi fechado, inclusive em toda ordem fixa. A certificação do VALOR
finito da observação crítica por esta rota continua aberta. Não há novo
teorema de positividade do pivô nem positividade Hankel all-order.

Base: `84687e5f5256c622c648254e559fbcba2c5128ae`, head da PR #60.
Branch: `agent/completed-readout-multiplier-bounds`.
A PR é empilhada sobre `agent/tfvd-infinite-fourth-tail`, não sobre uma
main que presumisse os merges anteriores. Main permanece
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Sem merge automático.
Somente `research/completed-readout-multiplier-bounds/` é acrescentado.

## A — O que já estava demonstrado

- A PR #41 constrói a funcional global, a forma bilinear e os polinômios
  mônicos. `NativeMomentOrthogonalization.orthogonalPolynomial_self`
  identifica o auto-pareamento com o pivô ALGÉBRICO, sem hipótese de sinal.
  A interpretação por inversa/Schur exige a não degenerescência original;
  divisão total em Lean não substitui inversibilidade.
- A #58 fornece os jets fortes do retorno original, sintetizados em ℓ¹,
  `CarryMaterialParts.return_jet_cells` e os dois canais beta/kappa.
- A #59 define literalmente `CarryCellTail.ordinaryMultiplier` e
  `clockMultiplier`, os coeficientes A=-D'/(2F), B=iD/(2F), e transporta o
  erro de cauda à MESMA direção crítica da #41.
- A #60 fecha o TFVD infinito, com a primeira correção de bordo e resto
  de quarta diferença. `CarryFourthTail.accelerated_native_moment_error`,
  `accelerated_bilinear_error` e `accelerated_critical_error` fornecem erro
  cúbico no cutoff. Suas constantes ainda continham normas de jets de A/B.
- `baseTwoCanonicalResponse_eq_dressing_mul_signal` identifica F=D*S;
  `baseTwoCriticalCompleteSignal` é a fonte completa com seed unitário e
  TODAS as células. A câmera, o dressing, Gamma e sua derivada são os
  preexistentes. Não foram ajustados.

A onda continua n^(-1/2)exp(-it log n), com pernas 4k+3, 4k+5 e centro
4k+4. O cutoff M é material; m é ordem de Taylor normalizada; n é ordem
polinomial. Nenhum desses índices é profundidade vertical. O raio complexo
usado nas estimativas de Cauchy não altera a fonte ou a métrica.

## B — O que foi demonstrado agora

Todos os nomes novos pertencem ao namespace `CarryReadoutBounds`.
São 59 teoremas e 11 definições, em sete módulos matemáticos. As declarações
Lean registram as hipóteses completas.

### 1. Inversão quantitativa da fonte completa

`SignalBounds.lean` define apenas a continuação complexa da soma original,
S(w)=1+sum_k complexCell(k,w). `complex_signal_real` identifica exatamente
sua restrição com `baseTwoCriticalCompleteSignal`. Não é uma fonte de cutoff.

`reciprocal_cells_bound`, `signal_deviation_bound`, `signal_norm_lower` e
`inverse_signal_bound` provam, para |w|≤1/2:

    sum_k 1/(4k+3)^2 ≤ 7/36,
    |S(w)-1| ≤ 7/18,
    |S(w)| ≥ 1/2,        |1/S(w)| ≤ 2.

A primeira estimativa usa a primeira célula mais a cauda racional da #59;
a segunda mantém cada segunda diferença inteira antes de tomar a norma.
`complex_signal_differentiableOn` prova a soma analítica no disco aberto.
O controle de inversão não usa positividade de momentos ou de pivôs.

### 2. Gamma e câmera originais

`GammaBounds.lean` demonstra `complex_gamma_norm_le_real` pela integral de
Euler da própria Gamma, e `real_gamma_le_inverse` pela convexidade de Gamma
entre 1 e 2 e sua recorrência. Não é uma integral theta ou outra representação
dos momentos. A reflexão de Gamma fornece o controle do inverso.
Para |w|≤1/4 e z=(1/2+iw)/2:

    1/8 ≤ Re z ≤ 3/8,     |Gamma(z)| ≤ 8,     |1/Gamma(z)| ≤ 8.

São `gamma_argument_bounds`, `gamma_factor_bound` e
`inverse_gamma_factor_bound`. Não se presume ausência de zeros de uma
característica espectral.

`CameraBounds.lean` conserva C(w)=(1+2^(-s))(1-2^(1-s)), s=1/2+iw.
`camera_inverse_factors` prova as separações dos DOIS fatores. Daí:

    |C(w)| ≤ 6,          |1/C(w)| ≤ 72,       C(w)≠0,

no mesmo disco de raio 1/4. Todos os números dessas envoltórias são racionais;
log 2 e log pi são limitados analiticamente, sem números ajustados à Hankel.

### 3. Cancelamento exato, preservando todos os fatores

`DressingBounds.lean` usa P=s(s-1)/2, E=exp(-s log pi/2), G=Gamma(s/2),
C=câmera original. `complex_dressing_formula` prova D=P*E*G/C.
`dressing_log_split` conserva exatamente

    D'/D = P'/P + E'/E + G'/G - C'/C.

As derivadas são complexas nessa continuação. `dressing_deriv_real` no módulo
seguinte prova o transporte para a derivada real original do dressing.

`derivative_eighth_bound` aplica Cauchy em círculos inteiramente contidos no
disco de raio 1/4. Com os inversos dos fatores, `dressing_log_bound` prova

    |D'(w)/D(w)| ≤ 8192,                     |w|≤1/8.

É uma cota deliberadamente larga: os quatro termos são majorados por
256, 72, 512 e 3456; sua soma é menor que 8192. Nenhum deles foi descartado.

`MultiplierBounds.lean` prova `ordinary_multiplier_real` e
`clock_multiplier_real`. Como F=D*S, os multiplicadores LITERAIS são

    A=-(D'/D)/(2S),        B=i/(2S).

O cancelamento de D é uma igualdade provada com seu não anulamento;
não é remoção do dressing de Q. Gamma e câmera continuam em D'/D.

`ordinary_multiplier_jet_bound` e `clock_multiplier_jet_bound` dão, sem
hipótese de sinal, para TODO j:

    |jet_j A| ≤ 8192*8^j,             |jet_j B| ≤ 4^j.

`first_six_multiplier_bounds` é a especialização às ordens 0…5 pedidas no
relatório anterior. São discos racionais centrados em zero, não caixas
estreitas dos valores dos coeficientes. Os jets incluem 1/j!.

### 4. Orçamento crítico inteiramente explícito

`ExplicitBudgets.lean` substitui as normas ainda desconhecidas por
`explicitResponseConstant`:

    Cbar_r = sum_{j≤r} 8192*8^j*2^(r-j+1)
           + sum_{j≤r} 4^j*(r-j+1)*2^(r-j+2).

`response_constant_le` prova C_r≤Cbar_r. Para r=0…5, os valores são
16388, 163872, 1376432, 11141952, 89394752, 715668480.
`explicit_moment_error` transporta-os ao MESMO h_n canônico:

    |h_n-hObs(M,n)| ≤ 5*Cbar_(2n+1)/[4(4M-1)^3],       M≥1.

`explicit_bilinear_error` trata DOIS argumentos independentes e todos os
pares i,j. Só depois `explicit_critical_error` especializa à direção
`criticalCoefficients` original da #41/#54. Não há whitening, nova Gram,
nova métrica, corte de quadratura ou hipótese de pivô positivo.

Na segunda direção par, escreva

    R(a)=h_2-2a*h_1+a^2*h_0,
    RObs(a,M)=hObs_2-2a*hObs_1+a^2*hObs_0.

`second_even_residual_error` conserva os cruzamentos e dá o orçamento
5*(Cbar_5+2|a|Cbar_3+|a|^2 Cbar_1)/[4(4M-1)^3].
`second_even_residual_eq_pivot` prova que, em a=h_1/h_0, R(a) é o pivô
algébrico original. O caso de denominador zero é separado na prova; não se
afirma inversibilidade nele.

`Canary.lean` prova `second_even_error_at_100000`:

    |a|≤1/100  ==>  |R(a)-RObs(a,100000)| < 1/50000000.

A envoltória racional mais precisa é
74572014107/5333293333433333250, aproximadamente 1.39823575e-8.
`second_even_critical_error_at_100000` especializa à razão h_1/h_0, mantendo
EXPLICITAMENTE a hipótese |h_1/h_0|≤1/100. Essa hipótese ainda não foi
descarregada por esta nova rota, e o teorema não afirma sinal positivo.

### 5. Canário finito da mesma fonte

`experiment.py` calcula somente os jets materiais 0…6, nos cutoffs 512,
4096, 100000 e 101000, com o bordo acelerado da #60. Usa o logaritmo da
Gamma original e os fatores explícitos de D para as operações numéricas.
Não recebe theta, zeros, alturas, checkpoints de momentos ou fatoração de
uma Hankel. A derivada logarítmica factorizada é confrontada com a derivada
da fórmula ORIGINAL de D em três pontos.

A referência FINITA 101000 estima os multiplicadores completos. Ela não é
um denominador completo certificado. Os resultados mpmath são regressões
numéricas, não intervalos certificados pelo kernel.

Resultados numéricos:

    h_0 ≈ 0.02310499311541897016,
    h_1 ≈ 0.00003717259928527666,
    h_2 ≈ 1.4417393140598658e-7,
    a   ≈ 0.001608855674597443,
    p   ≈ 8.436858410633238e-8.

Em M=100000, a observação numérica é aproximadamente
8.436858410661985e-8; a envoltória provada, avaliada nessa estimativa de a,
é aproximadamente 1.39787051e-8. Isso sugere folga para uma certificação
intervalar, mas NÃO constitui a certificação do valor da observação.
A discrepância de cerca de 2.9e-19 contra a referência finita tampouco é um
erro infinito certificado. Não se presume que aumentar DPS acrescente uma
prova dos valores transcendentes.

## C — O que foi refutado ou evitado

Não foi demonstrado um novo no-go físico. O cálculo não refuta a fonte nem
uma realização Gram completada.

Foi mantida a distinção decisiva: uma cota superior de norma dos
multiplicadores permite limitar o ERRO de cauda; ela não localiza os seus
VALORES perto das estimativas numéricas e não certifica o sinal de RObs.
Seria incorreto anunciar o pivô positivo somente porque a estimativa
numérica excede o orçamento racional.

Não identificamos uma fonte truncada com o denominador completo F. A prova
usa os A/B completos; a regressão numérica declara separadamente sua
referência finita. A decomposição Green HT+TH+TT da #60 permanece intacta;
não afirmamos que uma normalização finita de E(head,head) seja RObs.
H6/K6 e as doze fontes são somente regressões posteriores, bloqueadas nas
dependências dos resultados novos.

## D — Kernel, dependências e reprodução

**Validação completa: 18/18 verificações com código de saída zero.**
Os sete módulos matemáticos e Audit compilaram explicitamente com
warningAsError. Passaram os builds focado e raiz com `lake build --wfail`,
as três auditorias de camadas, a regressão das doze fontes, os controles
racionais e numéricos, a preservação histórica e `git diff --check`.

A auditoria gerada cobre as 70 raízes públicas, tipos e corpos, e imprime
`#print axioms` de todas elas. Os únicos axiomas permitidos são propext,
Classical.choice e Quot.sound. Guards rejeitam dependências dos certificados
H6/K6/H7, `material_scale_pos`, controles posteriores de sinal e consumidores
de positividade all-order. Os fechamentos transitivos medidos são:
Gamma 4647; sinal 3182; câmera 1684; dressing 4775; multiplicadores 4845;
orçamentos 5397; canários 5257.

Reprodução no ambiente preparado da PR #60, host llm:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/completed-readout-multiplier-bounds/validate.py
```

`compile_module.sh` explicita os caches dos ancestrais e compila os sete
módulos novos e Audit com warningAsError. A validação também roda o build
focado, `lake build --wfail` raiz, as auditorias Foundation/Geometry/Analysis,
a regressão das doze fontes, os controles racionais/numéricos e a preservação
de fontes/refs/pins/worktrees. Não instala dependências. Num ambiente novo,
preparar antes os ancestrais conforme seus relatórios. Os comandos, logs,
resultados e hashes ficam em `evidence/`.

O checkout do operador não recebe alterações. Seu HEAD e seus arquivos
preexistentes, a sobra não rastreada da #51, os módulos históricos e as refs
das PRs anteriores são protegidos pela validação. Nenhuma worktree foi criada.

## E — Próximo passo mínimo

O controle de inversão e as COTAS SUPERIORES dos multiplicadores já estão
provados: não precisam ser recebidos como hipóteses ou refeitos. O gate
restante é uma certificação dos VALORES finitos, na fonte original:

    |h_1/h_0| ≤ 1/100,
    RObs(h_1/h_0,100000) > 1/50000000.

Essas duas desigualdades, junto com o canário agora provado, fechariam o
sinal por esta rota. São metas concretas de certificação, não premissas
geométricas já demonstradas nem uma nova lei de positividade all-order.

Para descarregá-las economicamente: provar intervalos estreitos para os
jets 0…6 da Gamma(s/2) ORIGINAL (ou diretamente 0…5 de sua derivada
logarítmica); combiná-los com as fórmulas exatas dos outros fatores, os jets
materiais finitos e suas caudas já provadas. A inversão da série de S deve
continuar sendo a do S completo, com erro transportado. Também é possível
usar esses intervalos para estreitar as envoltórias largas de A/B e reduzir
o cutoff; isso seria apenas avaliação mais precisa da MESMA fonte.

A direção crítica da #41, incluindo os dois termos cruzados, continua sendo
o alvo. Não se deve substituir essa certificação por uma nova fatoração da
Hankel ou por uma medida positiva presumida.

Para all-order permanece aberta uma propriedade independente da síntese
física que oriente o sinal dos residuais. As estimativas em toda ordem fixa
fechadas aqui não são coercividade uniforme nem uma prova desse sinal.
