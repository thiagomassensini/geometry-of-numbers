# Missão Luna — pencil sigma assinado e correspondência de Padé

**Estado da missão: em andamento.** A–C estão provados e publicados. D é
condicional a uma hipótese explícita de continuação analítica. E agora prova em
Lean que uma decomposição original com resto exponencial controlado implica os
limites dos menores sigma e a convergência de uma raiz original para `zeta`;
a hipótese analítica que fornece esse resto ainda está aberta. F está
demonstrado para modelos auxiliares de par único deslocado e de dois polos
reais distintos. A grade numérica de G foi reproduzida.

## Proveniência e Git

Branch: `agent/native-sigma-pade-signed-pencil`.

SHA da base ao iniciar: `9c74f14195410a9221448917ae469f71b9dcfe0b`, igual ao
remoto `agent/native-raw-rank-one-deflation`. O worktree desta missão foi
criado independentemente nessa base. O checkout auxiliar Carry está sujo com
alterações preexistentes não relacionadas; elas foram preservadas.

- Checkpoint A: [commit `189de259`](https://github.com/thiagomassensini/geometry-of-numbers/commit/189de2599a84aa78e6a5b50b71d5aa0b9a4645b9).
- Checkpoint B: [commit `b2998c59`](https://github.com/thiagomassensini/geometry-of-numbers/commit/b2998c595df575e95de664085a083616ba094eec).
- Checkpoint C: [commit `c0a4998`](https://github.com/thiagomassensini/geometry-of-numbers/commit/c0a4998f8ae3bb2f0783c0d4258507db0e5d8b5d).
- A ponta remota foi conferida após cada push.

## PROVADO — A: pencil assinado original

`SigmaSignedPencil.lean` define

\[
G_s(d)=\texttt{sigmaMatrix}(d,s,2),\qquad
K_s(d)=\texttt{sigmaMatrix}(d,s+1,2),\qquad
A_s(d)=G_s(d)^{-1}K_s(d).
\]

`CarrySigmaPade.sigmaPencil_metricSelfAdjoint` prova, sob `IsUnit G_s(d)`
somente,

\[
G_sA_s=K_s=A_s^\top G_s.
\]

O teorema não supõe `PosDef`; a métrica pode ser indefinida. O resultado usa
que as duas janelas `sigmaMatrix` originais são simétricas.

`CarrySigmaPade.hermitian_generalizedEigenvector_isotropic` prova para
quaisquer matrizes Hermitianas complexas que

\[
Kv=\lambda Gv,\quad \operatorname{Im}\lambda\ne0
\quad\Longrightarrow\quad v^*Gv=0.
\]

Isso prova isotropia do vetor. Não identifica esse vetor com o núcleo de
`G`.

## PROVADO — B: identidade exata pencil–Padé

Os coeficientes são lidos diretamente de `completedSigmaLogJet d n`, a mesma
sequência usada por `sigmaMatrix`; nenhum zero ou espectro é usado para
construir momentos. `sigmaPadeD`, `sigmaPadeB` e `sigmaPadeC` são exatamente

\[
D_s=h_sh_{s+2}-h_{s+1}^2,\quad
B_s=h_sh_{s+3}-h_{s+1}h_{s+2},\quad
C_s=h_{s+1}h_{s+3}-h_{s+2}^2.
\]

`sigmaPencilCharacteristic_eq_quadratic` demonstra

\[
\det(K_s-\lambda G_s)=D_s\lambda^2-B_s\lambda+C_s.
\]

Sob `D_s ≠ 0`, `alpha=B_s/D_s`, `beta=C_s/D_s`, e o denominador
`q_s(u)=1-alpha u+beta u²` é formalizado sobre a série original
`PowerSeries.mk (completedSigmaLogJet d)`. `sigmaOriginalMomentSeries_is_pade`
prova o critério em coeficientes para um aproximante `[s+1/2]`: numerador de
grau no máximo `s+1`, denominador normalizado de grau no máximo `2`, e
`q_s G_d-p_s` nulo até a ordem `s+3`. As duas equações de cancelamento nas
ordens `s+2` e `s+3` são teoremas Lean separados. Não há hipótese de
positividade nem de informação sobre zeros.

No plano complexo, `sigmaPencil_root_classification` dá a correspondência
completa quando `D_s ≠ 0`:

- cada raiz não nula `lambda` do pencil corresponde exatamente à raiz
  `u=lambda⁻¹` de `q_s`, e vice-versa;
- `lambda=0` é raiz do pencil exatamente quando `C_s=0`. Nesse caso, o
  denominador Padé cai de grau e a raiz restante é a raiz projetiva no
  infinito. Se `C_s ≠ 0`, todas as raízes do pencil são recíprocas de raízes
  finitas do denominador.

Isso explicita o caso degenerado que não pode ser descartado apenas de
`D_s ≠ 0`.

## Auditoria e reprodução

`SigmaPadeAudit.lean` audita 105 raízes públicas e percorre 59.325 constantes
alcançáveis nos tipos e corpos. Foram aceitos somente os axiomas-base do Lean
`[propext, Classical.choice, Quot.sound]`. A auditoria exige como dependências
`sigmaMatrix`, `completedSigmaLogJet` e
`completedNativeOperatorCharacteristic`, confirmando a proveniência original.

```bash
cd /home/thlinux/worktrees/geometry-of-numbers-native-sigma-pade-signed-pencil
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaSignedPencil
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeCorrespondence
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaTwoPoleModel
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaZeroPairDecomposition
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeConvergence
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeAudit
```

O script usa os caches Lean históricos e permite configurar
`SIGMA_REFERENCE_ROOT` e `CARRY_LEAN_ROOT`. O diretório de cache local
`.cache/` não é versionado e foi preservado.

## PROVADO — C: modelo auxiliar de dois polos

`SigmaTwoPoleModel.lean` declara explicitamente que sua sequência
`twoPoleMoment m zeta n = m * Re(zeta^(n+1))` é auxiliar e não a identifica com
`completedSigmaLogJet`. `twoPoleGram_det` prova, para todo deslocamento `s`,

\[
\det G_s^{\rm par}=-m^2(\operatorname{Im}\zeta)^2
  (\operatorname{normSq}\zeta)^{s+1}.
\]

`twoPolePencil_characteristic` fatora o determinante complexo do lápis como
`det(G_s) * (lambda-zeta) * (lambda-conj(zeta))`. Para
`zeta=(gamma+i delta)^(-2)`, `inverseSquare_twoPoleGram_det` dá

\[
-\frac{4m^2\gamma^2\delta^2}{(\gamma^2+\delta^2)^{2s+6}}.
\]

Quando `m>0`, `gamma>0` e `delta≠0`, `inverseSquare_twoPole_negative_direction`
produz um vetor com forma quadrática negativa; `inverseSquare_twoPole_roots`
certifica as duas raízes características conjugadas, distintas e não-reais.
`inverseSquare_roots_recover_height` exibe raízes quadradas inversas com parte
real `gamma` e partes imaginárias `delta` e `-delta`, recuperando
`gamma+i delta` e `gamma-i delta`. Esses resultados verificam o mecanismo do modelo; não atribuem
nenhuma contribuição de polos ao sigma original.

O módulo também formaliza o limite de deslocamento zero com dois polos reais
distintos. Para pesos `m₁,m₂>0` e nós `ρ₁,ρ₂>0`, `ρ₁≠ρ₂`,
`twoRealPoleGram_det` dá

\[
\det G_s=m_1m_2(\rho_1\rho_2)^{s+1}(\rho_1-\rho_2)^2>0,
\]

e `twoRealPolePencil_characteristic` fatora o determinante pelas raízes
exatas `ρ₁,ρ₂`, para todo `s`. Isso formaliza o lado `d=0` do modelo de dois
polos; não identifica essa sequência auxiliar com os jatos sigma.

## CONDICIONAL — D: fator local do zero e resto para os jatos originais

`SigmaZeroPairDecomposition.lean` preserva a fonte
`completedNativeOperatorCharacteristic` e a sequência original
`completedSigmaLogJet`. `completedNativeF_positive_zero_factorization` usa
analiticidade já disponível na altura real e a hipótese explícita de ordem
analítica exata `m`; daí obtém localmente

\[
F(z)=(z-\gamma)^m g(z),\qquad g(\gamma)\ne0.
\]

Em seguida, `completedNativeLogResponse_local_factorization` prova na vizinhança
perfurada

\[
Q(z)=-\frac{m}{2(z-\gamma)}-\frac{g'(z)}{2g(z)},
\qquad Q=-F'/(2F).
\]

O teorema condicional liga essa identidade local à geradora original. Ele exige
um certificado de Taylor para o modelo racional de polos conjugados e uma
decomposição local da geradora como esse modelo mais a série residual construída
dos próprios jatos sigma. Para algum raio testemunha `rho`, exige ainda

\[
1/|\zeta|<\rho<R_{\rm rem},\qquad
\zeta=(\gamma+id)^{-2},\quad 0<d<1/4.
\]

Então a unicidade da série de Taylor dá
`h_n = m * Re (zeta^(n+1)) + r_n` e a estimativa de Cauchy dá
`|r_n| ≤ C * eta^n` com `eta = 1/rho < |zeta|`. A restrição `d<1/4` mantém
as duas alturas deslocadas dentro do domínio nativo complexo já certificado;
os jatos originais continuam definidos no intervalo maior `|d|<1/2`.

**Não foi provado** que a característica completada satisfaz a hipótese de
continuação `hdecomp`, nem que um zero positivo de ordem finita exista. Logo D
não atribui contribuição de polos à fonte original sem essas hipóteses. A
continuação e a separação espectral permanecem condicionais.

## NUMÉRICO — G: extração Cauchy independente

`completedNativeOperatorCharacteristic` preserva literalmente a fatoração
`F=A·N`: o fator arquimediano nativo multiplica `nativeScalar`. O teorema
`completedNativeOperatorCharacteristic_eq_completedRiemannZeta` identifica
`N` com `zeta(s)` no strip crítico aberto. Para obter os momentos por Cauchy,
o script avalia a continuação clássica desse mesmo germe,
`F(z)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)`, `s=1/2+i*z`, e calcula
analiticamente `Q=-F'/(2F)`. Perto de `u=0`, para os deslocamentos testados,
os pontos pertencem ao strip onde a igualdade nativa foi provada; os círculos
de Cauchy completos ultrapassam esse strip. Essa continuação é usada como
extensão numérica do mesmo germe, mas não foi certificada em Lean em todo o
disco nem recebe certificado intervalar. Um ponto de controle compara a
derivada logarítmica analítica com `-mp.diff(F,z)/(2F(z))`.

Foram extraídos os dois ramos do pencil nos dois contornos `|u|=100` e
`|u|=150`, com 256 pontos trapezoidais por contorno e 100 dígitos, para todas
as combinações `s=10,15,20,30,40,50` e
`d=0.2,0.1,0.05,0.02,0.01,0`. As alturas conhecidas não entram na extração.
Para `d=0.2`, a raiz inferior recuperada é
`14.1347251417334538384−0.1999999999962239424i` em `s=40` e
`14.1347251417346937506−0.1999999999999988489i` em `s=50`, reproduzindo as
referências experimentais fornecidas. Em `d=0`, os dois ramos em `s=40` dão
`14.1347251417346937905` e `21.0220427324547918603`; em `s=50`, dão
`14.1347251417346937905` e `21.0220397345794759398`. Após a extração, a segunda
altura de `d=0,s=50` difere em cerca de `9.58e-8` do segundo zero tabelado.
Esse comportamento numérico é compatível com os dois limites distintos
previstos em F. A diferença máxima entre as alturas obtidas pelos dois
contornos em toda a grade foi `2.31e-31`.

Essas diferenças medem concordância numérica entre quadraturas, não um limite
de erro certificado nem prova de ausência de polos nos discos. Não provam a
continuação global requerida por D, a convergência assintótica de E ou os
limites iterados de F. A LMFDB documenta os primeiros 103.800.788.359 zeros e
sua precisão de `±2.5e-31`; as alturas de comparação só foram consultadas após
a extração ([LMFDB, zeros de zeta](https://www.lmfdb.org/zeros/zeta/),
[FLINT, tutorial numérico e primeiros zeros](https://fredrikj.net/fdoc/html/tutorials/numerics/zeta.html)).

Reprodução:

```bash
python3 research/native-moving-schur-sigma/sigma_pade_cauchy_validation.py \
  > research/native-moving-schur-sigma/evidence/SigmaPadeCauchyValidation.csv
```

## CONDICIONAL — E: convergência das raízes em janelas móveis

`SigmaPadeConvergence.lean` prova dois passos gerais. Primeiro, se
`|r_n| ≤ C eta^n` com `eta<a`, então para cada deslocamento fixo `k`,
`r_(s+k)/a^(s+1) → 0`. Segundo, a fórmula complexa da raiz quadrática é
contínua em coeficientes normalizados quando o coeficiente líder tende a um
valor não nulo; quando `4AC-B² ≥ 0`, a fórmula satisfaz a equação quadrática.
`sigmaPadeOriginalNormalizedRoot_tendsto` enuncia isso diretamente para os
coeficientes originais `sigmaPadeD/B/C`, construídos dos jatos
`completedSigmaLogJet`; `sigmaPadeOriginalRoot_tendsto` também inclui o fator
de escala `a` para a raiz característica sem normalização.

Sob as hipóteses condicionais de D, escreva `zeta=a theta`, com
`a=|zeta|`, `theta=x+i y`, `|theta|=1` e `y≠0`. Para cada `k` fixo, a
decomposição e o lema de resto dão

\[
\frac{h_{s+k}}{a^{s+k+1}}
 = m\,\operatorname{Re}(\theta^{s+k+1})+o(1).
\]

Os termos principais são uniformemente limitados, então os termos de erro
desaparecem também nos produtos que definem os três menores. As identidades
trigonométricas do par conjugado dão

\[
\frac{D_s}{a^{2s+4}}\to-m^2y^2,\qquad
\frac{B_s}{a^{2s+5}}\to-2m^2xy^2,\qquad
\frac{C_s}{a^{2s+6}}\to-m^2y^2.
\]

Como `y≠0`, o coeficiente líder limite não zera e as duas raízes limite são
distintas. Para `X=lambda/a`, o polinômio normalizado tende a
`-m²y² (X²-2xX+1)`, cujas raízes são `theta` e `conj theta`. A fórmula
formalizada seleciona a raiz de parte imaginária negativa; para
`zeta=(gamma+i d)^(-2)` com `gamma,d>0`, ela converge a `zeta`, e a outra raiz
converge a `conj zeta`. Pelo checkpoint B, as raízes finitas do denominador
Padé são as recíprocas, portanto convergem a `1/zeta` e `1/conj zeta`. As
raízes quadradas locais recuperam `gamma±i d`.

A formalização agora prova a passagem do resto aos menores. O lema de
perturbação de produtos usa a limitação uniforme dos momentos do modelo na
circunferência unitária; `twoPoleMoment_abs_le_of_normSq_eq_one` prova essa
limitação. Assim, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder`
deduz diretamente do limite exponencial do resto os três limites
normalizados exibidos acima, para os menores da sequência
`completedSigmaLogJet`. Não se toma uma sequência de momentos auxiliar no
lugar da fonte.

Com esses limites, `sigmaPadeOriginalPencil_root_tendsto_to_twoPole` prova que
a raiz selecionada do pencil original é eventualmente não real, satisfaz a
característica exata e converge para `zeta` quando `Im(theta)<0`; essa é a
orientação de `zeta=(gamma+i d)^(-2)` para `gamma,d>0`. A identidade B implica
então a convergência da raiz correspondente do denominador de Padé para
`1/zeta`. O modelo auxiliar prova a recuperação exata de `gamma±i d` por
raízes quadradas inversas. A continuidade do ramo de `lambda^(-1/2)` para a
sequência original não foi formalizada como um teorema separado.

E continua condicional a `hdecomp`, ao zero positivo de ordem finita e ao
certificado de continuação de D. A prova Lean recebe o limite exponencial do
resto como hipótese; não afirma que a característica sigma satisfaz essas
hipóteses.

## CONDICIONAL NO MODELO; ABERTO NA FONTE — F: polos distintos e limites iterados

Para um primeiro par simples em `gamma₁±id`, o modelo de par conjugado tem
raízes características `zeta₁=(gamma₁+id)⁻²` e `conj(zeta₁)` em cada janela
quando `d≠0`. Ao fazer `d→0`, as duas raízes recíprocas quadradas convergem a
`gamma₁`. No modelo de dois polos reais distintos no ponto `d=0`,
`twoRealPolePencil_real_roots` prova que as raízes do pencil são exatamente
`rho₁=gamma₁⁻²` e `rho₂=gamma₂⁻²` para todo deslocamento, sob pesos positivos e
`gamma₁≠gamma₂`. Assim, para uma geradora que satisfaça as hipóteses de
dominância dos dois primeiros polos e estabilidade sob o resto, a previsão dos
limites iterados é

\[
\lim_{d\to0}\lim_{s\to\infty}\{T_{s,1}(d),T_{s,2}(d)\}
=\{\gamma_1,\gamma_1\},\qquad
\lim_{s\to\infty}\lim_{d\to0}\{T_{s,1}(d),T_{s,2}(d)\}
=\{\gamma_1,\gamma_2\}.
\]

O primeiro limite usa dominância do primeiro par para todo `d>0`; o segundo
usa dois nós reais distintos em `d=0`. A diferença é uma não comutatividade
genuína do limite com a extração assintótica quando há um segundo polo
separado. Ela não aparece no modelo de um único par, em que ambos os ramos
coalescem para a mesma altura.

Para a fonte sigma inteira, essa conclusão exige zeros simples e isolados em
`gamma₁<gamma₂`, ausência de outros polos de raio igual ou maior na
continuação relevante, um resto com raio estritamente menor que o segundo
raio, e continuidade suficiente em `d` para cada janela finita. Essas
hipóteses não foram descarregadas nem certificadas para
`completedNativeOperatorCharacteristic`; os limites iterados na fonte seguem
**ABERTOS**.

As três primeiras detecções são distintas. O menor principal inicial pode
falhar sem indefinição positiva (por exemplo `diag(0,1)` ainda é
semidefinida positiva); uma direção negativa pode coexistir com raízes reais
(`G=K=diag(1,-1)`); e um pencil pode ter raízes não reais (`G=diag(1,-1)`,
`K=[[0,1],[1,0]]`). No modelo de par conjugado, o determinante negativo e as
raízes não reais aparecem na janela de ordem 2 para todo `d≠0`. A falha
principal em ordem 1 depende do sinal de `h_s`: ocorre imediatamente se
`h_s<0`; se `h_s≥0`, o determinante negativo força a falha na ordem 2. Para
polos distintos com resto, não há nesta entrega uma estimativa quantitativa da
primeira janela; uma estimativa exige limitar explicitamente a razão entre o
segundo e o terceiro raios e controlar os coeficientes do resto.

## PUBLICADO E REPRODUÇÃO

Os checkpoints A–G estão publicados na branch
`agent/native-sigma-pade-signed-pencil`; os commits e SHAs finais são
registrados na resposta de entrega. Para reproduzir os módulos Lean, defina
`SIGMA_REFERENCE_ROOT=/home/thlinux/geometry-of-numbers-native-moving-schur-sigma`
e execute `compile_sigma_pade.sh` para cada módulo listado na seção de
auditoria. A extração numérica é reproduzida pelo comando acima. A auditoria
continua exigindo proveniência de `sigmaMatrix`, `completedSigmaLogJet` e
`completedNativeOperatorCharacteristic`, sem construir momentos a partir de
zeros conhecidos.
