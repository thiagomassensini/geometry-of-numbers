# Quinto setor ímpar, dez fontes e padrão theta em ordem arbitrária

## Resultado

O quinto teste ímpar foi certificado a partir da fonte theta infinita, com todas as caudas. Juntando-o ao quinto teste par do PR #27, os dois blocos de momentos 5 por 5 são definidos positivos. Isso fornece controle eventual do retorno de dez fontes e uma realização física dos jets canônicos de índices 0 a 9, com todos os seus cruzamentos.

Também foram formalizados resultados válidos em ordem arbitrária:

- A fórmula theta do próximo coeficiente e a alternância de orientação entre os setores par e ímpar.
- A diferença exata, com o acoplamento antigo completo, cujo sinal equivale à próxima margem física.
- Uma estimativa explícita para os infinitos modos omitidos, para qualquer quantidade de modos retidos e qualquer ordem.
- Uma escolha crescente de K(j) que controla todos os momentos theta de um bloco pelo mesmo prefixo de modos, para tolerâncias positivas prescritas.
- Um cutoff de integração dependente da ordem que controla a cauda de cada modo retido em qualquer ordem.

Esses resultados não demonstram positividade da hierarquia inteira. O controle absoluto das caudas não fornece a margem positiva da diferença completa de Schur em cada ordem.

## Proveniência

Base: `geometry-of-numbers`, main em `d4f7c0da8149a35c0fe976abc847b57d1bcb8ca7`, após PR #27. O operador foi consultado em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, sem alterá-lo.

Foram reutilizados os módulos dos PRs #23 a #27, particularmente:

- `TabledSourceEquivalence` e os caches de nós e coeficientes de quadratura já certificados.
- Os limites e estimativas dos modos theta reais da fonte original.
- A recorrência logarítmica canônica e a eliminação ordenada de `CarryMaterialSourceFactor`.
- As coordenadas críticas, a comparação entre balanço físico e pivô e a realização dos canais Green corrigidos.
- O retorno chiral, suas portas e as transições entre blocos do PR #26.

A fonte, amplitudes, métricas, pesos, dressing e pins anteriores permanecem preservados. Nenhum vetor físico foi definido por uma fatoração escolhida do Gram-alvo.

## Índices

| Símbolo | Significado |
|---|---|
| s | Setor par ou ímpar, 0 ou 1 |
| n | Tamanho do prefixo de Schur |
| d=2n+s | Índice do próximo momento logarítmico |
| p | Grau do peso de um momento theta |
| M | Quantidade de modos theta retidos |
| j | Metade da ordem de um momento theta par |
| L | Cutoff de integração de um modo theta |
| k | Regularização radial do retorno físico |
| N | Número de fontes incidentes do retorno |

M, N, j e n não representam câmeras ou profundidades físicas. A função K(j) abaixo é uma quantidade de modos theta para controle de erro, não um índice espectral.

## 1. O certificado do quinto setor ímpar

A infraestrutura anterior tinha demonstrado a inclusão de seus intervalos theta até ordem 18. A quadratura subjacente, entretanto, já era parametrizada pelo grau do peso. Os mesmos nós e coeficientes de Taylor servem para o peso de ordem 20.

`mem_tabledTheta_upto_twenty` estende a prova que reúne os modos e suas caudas até essa ordem, usando as mesmas três famílias de nós, grid 64, cutoffs 96/64, 64/64 e 48/64 e grau de Taylor 15. A inclusão da nova caixa é reduzida pelo kernel em `thetaTwenty_containment_check`.

A partir de I20 e dos intervalos anteriores, obtêm-se c10 e h9 pela característica e pela recorrência logarítmica originais. Não se substitui a fonte pelo truncamento de três modos: as caudas dos três modos e os infinitos modos omitidos continuam nos intervalos.

O quinto pivô da eliminação ordenada do bloco deslocado satisfaz o certificado estrito

\[
\frac{7}{10^{30}}<
\operatorname{carryPairingPivot}(\operatorname{carryMaterialOddPairing},4)
<\frac{10}{10^{30}}.
\]

A declaração é `fifth_ordered_odd_pivot_bounds`. Esses limites são do pivô da eliminação ordenada. A margem física abaixo é transportada pela positividade do bloco, sem anunciar um novo intervalo numérico para ela.

As cinco verificações de pivôs mantêm os acoplamentos da recorrência. Elas fornecem

\[
K_5=(h_{i+j+1})_{0\le i,j<5}>0.
\]

O PR #27 já fornecia H5>0. A nova conclusão é a positividade dos DOIS setores, não apenas de suas diagonais.

Declarações centrais: `mem_thetaTwentyBox`, `odd_five_rectangle_check`, `odd_source_five_posDef`, `fifth_odd_pivot_pos`, `fifth_odd_criticalMargin` e `fifth_odd_theta_integral_certificate`.

## 2. Consequência física: dez fontes

`finiteBoundary_positive_iff_sectorMatrices` estabelece a interface em dimensão fixa:

\[
\mathcal B_{2n}(x)>0\quad(x\ne0)
\iff H_n>0\ \text{e}\ K_n>0.
\]

A separação real/imaginária é aplicada às duas quadraturas de cada setor. A prova usa as fases existentes e a identidade de bordo original; não muda a métrica.

Para n=5, os certificados reais dos dois setores alimentam a estimativa de retorno existente. Segue

\[
\|T_{k,10}\|\le1\quad\text{eventualmente em }k.
\]

Isso é `ten_return_eventually_contractive`. A estimativa vale também para os prefixos de até dez fontes. A prova não calcula um valor numérico do cutoff radial.

As portas físicas e o limite compacto já construídos fornecem uma família única de dez vetores residuais no L2 original. A recomposição do canal central satisfaz o Gram canônico inteiro dos jets 0..9:

\[
\langle V_a,V_b\rangle=\operatorname{polarizedGreenMomentCoefficient}(h,a,b).
\]

`canonical_ten_physical_realization` é essa identificação. Os índices pares realizam H5 e os ímpares K5. A regressão `ten_block_calibration` verifica o centro, as duas novas diagonais, o cruzamento 7–9 e o cruzamento misto 8–9.

`eight_to_ten_residual_crossings` conserva todos os cruzamentos antigos em regularização finita pelas transições físicas existentes. `ten_nested_physical_realization` escolhe a família de dez uma só vez e restringe seus prefixos. Eles permanecem no carrier de dez fontes; não se afirma pertencimento ao menor espaço anterior.

## 3. O padrão da fonte em qualquer ordem

Escreva c_r para o coeficiente par original da característica completada e I_p para o momento theta completo. Para

\[
d=2n+s,\quad r=d+1,\quad
A=(h_{i+j+s})_{i,j<n},\quad b=(h_{i+n+s})_{i<n},
\]

ponha

\[
C_{s,n}=-\frac{\sum_{k<d}h_kc_{d-k}+c_0b^TA^{-1}b}{r}.
\]

Esse é `sourceCeiling`. O termo de realimentação de TODAS as fontes antigas permanece explícito.

A mesma identidade theta vale para qualquer d:

\[
J_d=\int_0^\infty
\bigl(4(2d+2)(2d+1)u^{2d}-u^{2d+2}\bigr)\theta_{\rm tail}(u)\,du,
\]

\[
c_r=\frac{(-1)^{s+1}J_d}{4(2d+2)!}.
\]

Ela é provada em `sourceCoefficient_theta` e `sourceCoefficient_parity` a partir da ponte all-order existente entre Xi e theta. Nenhuma nova fonte positiva é escolhida.

Há uma identificação adicional com um resultado positivo já disponível:

\[
J_d=4\,\operatorname{completedNativeXiCosineMoment}(d+1)>0.
\]

`sourceThetaIntegral_eq_xiMoment` e `sourceThetaIntegral_pos` transportam essa positividade em todas as ordens. Ela é a positividade dos momentos do kernel Xi, não a positividade da Hankel dos momentos LOGARÍTMICOS h.

Sob positividade do prefixo antigo,

\[
\text{próxima margem física}>0
\iff
(-1)^{s+1}J_d<4(2d+2)!C_{s,n}.
\]

Portanto o setor par exige uma estimativa INFERIOR para J, enquanto o ímpar exige uma estimativa SUPERIOR. A orientação não permanece fixa quando intercalamos os passos.

Os pesos anteriores \(1224u^{16}-u^{18}\) e \(1520u^{18}-u^{20}\) são recuperados literalmente como d=8 e d=9 nas regressões.

## 4. A diferença exata que falta controlar globalmente

Defina, apenas como leitura da fonte e de seus acoplamentos,

\[
G_{s,n}=4(2d+2)!C_{s,n}-(-1)^{s+1}J_d.
\]

A identidade sem divisão é

\[
\boxed{c_0\,4(2d+2)!\,\sigma_{s,n}=rG_{s,n}.}
\]

Ela é `sourceSchur_thetaGap`. A sua ligação com os estados físicos é

\[
c_0\,4(2d+2)!\bigl(\|X_k\|^2-\|T_kX_k\|^2\bigr)
\longrightarrow2rG_{s,n}.
\]

O teorema `physicalThetaGap_tendsto` conserva o balanço incidente/retorno original. Os fatores são os da fonte e das identidades anteriores.

`criticalMargin_iff_thetaGap` prova que a próxima margem persistente equivale a G>0, sob positividade do prefixo antigo. `allSourceThetaGates_returnBounds` alimenta a torre física em toda ordem CONDICIONALMENTE à família dessas desigualdades. O sinal geral de G não é demonstrado nesta rodada.

## 5. Caudas para qualquer quantidade de modos e qualquer ordem

Sejam M os modos theta retidos. O resto usado é a diferença REAL da fonte:

\[
\mathcal T_{M,p}=\int_0^\infty
\left(u^p\theta_{\rm tail}(u)-\sum_{m<M}u^p\operatorname{thetaMode}_m(u)\right)du.
\]

`theta_prefix_split` prova a decomposição exata para qualquer M; `weightedOmittedPrefix_eq_tail` identifica o resto com os modos efetivamente omitidos. Não se introduz um tail independente.

Com constantes de majorante derivadas da fonte,

\[
a_M=\frac{2e^{-3(M+1)^2}}{1-e^{-6(M+1)}},\qquad
\rho_M=6(M+1)^2-\frac12,
\]

foram provadas as estimativas

\[
0\le\mathcal T_{M,p}\le a_M\frac{p!}{\rho_M^{p+1}}
\le\boxed{4p!e^{-3(M+1)}}.
\]

Elas valem para TODO M,p. Os nomes são `integral_weightedOmittedPrefix_bounds` e `omittedPrefix_geometric_bound`. a_M é uma constante de estimativa demonstrada, não uma nova amplitude da fonte.

Para a cauda de cada modo retido, o cutoff L=p+1 satisfaz

\[
2\operatorname{thetaArgument}_m(L)-\frac12-\frac pL
\ge\frac{33}{2}+12p>0.
\]

`retained_tail_bound_all_orders` controla assim a integral de L até infinito em qualquer ordem. L é cutoff de integração, não regularização radial ou profundidade.

## 6. Uma escolha comum de K(j) para os blocos

`exists_monotone_common_mode_schedule` demonstra:

\[
\forall(\varepsilon_j>0)\ \exists K\text{ estritamente crescente},\quad
\mathcal T_{K(N),2j}<\varepsilon_j\quad\text{para todo }j\le N.
\]

Assim, TODOS os momentos de um bloco usam o MESMO prefixo de modos, e esses prefixos crescem entre blocos. Isso é mais forte que escolher truncamentos independentes para cada entrada.

A construção escolhe limiares de erro e toma máximos finitos. Não calcula o menor K nem fornece um cutoff universal fixo. As tolerâncias são dados de precisão, não margens de positividade assumidas para o problema.

Para aplicar o esquema à etapa (s,n), os momentos theta necessários têm índices j=d e j=d+1. Uma escolha comum que cubra esse bloco preserva a mesma fonte. Isso não identifica índice theta, câmera e índice material.

## 7. O que o padrão resolve — e o que ainda falta

O padrão fornece identidades e controle absoluto das caudas em toda ordem. A fonte continua completa e os coeficientes são transportados pela recorrência original.

O ponto não resolvido é a margem de G. Ela inclui a soma antiga e \(b^{\mathsf T}A^{-1}b\). O controle de erro nessa parcela depende também do inverso do prefixo antigo. Não foi demonstrada uma estimativa conjunta que sustente G>0 em todas as ordens.

A positividade de J, a convergência das caudas e a possibilidade de escolher K(j) não fornecem, sozinhas, essa comparação. O esquema de intervalos de precisão fixa também não é anunciado como certificado não trivial em todas as ordens.

O primeiro próximo alvo finito, agora precisamente tipado, é o sexto teste par:

\[
J_{10}=1848I_{20}-I_{22},\qquad
J_{10}>-4\,22!\,C_{0,5}.
\]

`next_even_margin_gate` e `next_even_theta_weight` deixam essa obrigação explícita. O certificado até dez fontes não fornece o sinal dessa nova diferença.

## Status

| Status | Resultado |
|---|---|
| PROVADO | Inclusão do momento theta de ordem 20, com caudas infinitas |
| PROVADO INCONDICIONAL | Quinto pivô ímpar positivo e dois blocos 5 por 5 positivos |
| PROVADO INCONDICIONAL | Retorno eventualmente contrativo até dez fontes; realização física dos jets 0..9 |
| PROVADO | Cruzamentos e prefixos físicos compatíveis até dez fontes |
| PROVADO PARA TODA ORDEM | Fórmula theta e sua alternância par/ímpar; identificação com o momento Xi positivo |
| PROVADO PARA TODA ORDEM | Estimativas das caudas omitidas e retidas e escolha comum crescente K(j) para tolerâncias prescritas |
| CONDICIONAL | Positividade/retorno em toda ordem sob a família de diferenças G positivas |
| ABERTO | Margem do sexto teste par e controle conjunto de G para n arbitrário |

## Validação

PASS: oito módulos, 75 declarações públicas com auditoria transitiva por tipos e corpos, regressões, build raiz `--wfail` com 8841 jobs e auditorias das três zonas.

Reprodução no servidor llm:

    bash research/theta-fifth-odd-pattern/audit-theta-fifth-odd-pattern.sh

O script recompila os oito módulos novos com avisos como erros, audita todos os nomes públicos por tipos e corpos, executa regressões, o build raiz `lake build --wfail` e as auditorias Foundation, Geometry e Analysis.

As dependências históricas usam caches compilados com fontes, commits e pins conferidos. Não se anuncia recompilação fresca dessas dependências. Os módulos desta rodada são recompilados.

Os hashes das fontes e logs estão em `evidence/source-manifest.json` e `evidence/validation.json`. `evidence/Audit.log` registra os axiomas de cada declaração. A política permite somente os três axiomas padrão da zona Analysis; não foram introduzidos axiomas adicionais, provas admitidas ou escapes de confiança.
