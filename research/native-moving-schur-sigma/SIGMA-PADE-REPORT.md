# Missão Luna — pencil sigma assinado e correspondência de Padé

**Estado da missão: em andamento.** Os checkpoints A–C estão provados em
Lean, compilados com `-DwarningAsError=true`, auditados transitivamente e
publicados. D foi formalizado sob hipóteses explícitas de continuação. E–F e a
validação numérica continuam em andamento.

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

`SigmaPadeAudit.lean` audita 72 raízes públicas e percorre 59.140 constantes
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

## NUMÉRICO — extração Cauchy independente

`sigma_pade_cauchy_validation.py` avalia a característica original completada
pela fórmula
`F(z)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)`, `s=1/2+i*z`, e usa seu
logaritmo derivado analítico para `Q=-F'/(2F)`. Um ponto de controle compara
essa fórmula com `-mp.diff(F,z)/(2F(z))`. Os jatos são extraídos de
`G_d(u)=sigmaTransverseMean(Q,sqrt(u),d)/sqrt(u)` por integrais de Cauchy nos
círculos `|u|=100` e `|u|=150`, com 128 pontos trapezoidais por círculo. As
alturas conhecidas não aparecem como entrada do script.

Após a extração, os resultados foram comparados com o primeiro zero da tabela
pública LMFDB, `gamma_1 = 14.134725141734693790...`. Para `d=0.1`, a altura
recuperada na janela `s=24` é aproximadamente
`14.1347188561048563 + 0.0999973368245615 i`; para `d=0.2`, é
`14.1347240316165533 + 0.1999988544136233 i`. Os erros em relação a
`gamma_1+i*d` são, respectivamente, `6.29e-6` e `1.11e-6` na parte real, e
`2.66e-6` e `1.15e-6` na parte imaginária. Entre os dois contornos, a diferença
na altura de `s=24` é `7.9e-22` para `d=0.1` e `1.8e-22` para `d=0.2`.

Isso é uma verificação numérica independente e reproduzível, não um limite de
erro certificado: não prova a continuação analítica de D nem a convergência
assintótica de E. A tabela LMFDB relata os primeiros 103.800.788.359 zeros e
precisão de `±2.5e-31`; os valores de comparação foram consultados somente
depois da extração ([LMFDB, zeros de zeta](https://www.lmfdb.org/zeros/zeta/),
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

A formalização já cobre a estimativa do resto, a continuidade da fórmula e a
equação quadrática. O cálculo dos três limites dos menores a partir da
decomposição foi verificado algebricamente aqui, mas ainda não está codificado
como um teorema Lean. E permanece condicional a `hdecomp`, ao zero positivo de
ordem finita e ao certificado de continuação de D; não afirma que esses fatos
foram estabelecidos para a característica sigma.

## PROVADO NO MODELO AUXILIAR; ABERTO NA FONTE — F: limites e primeira detecção

No modelo de dois polos, para todo `d≠0`, o determinante de cada janela é
estritamente negativo, a forma tem uma direção negativa e o lápis regular de
ordem 2 tem raízes não reais. Para `zeta=(gamma+i d)^(-2)`, elas são
`zeta` e `conj zeta` para todo deslocamento `s`, e ambas tendem a
`gamma^(-2)` quando `d→0`. O determinante tende a zero. Em `d=0`, a matriz
de Gram é singular e o determinante característico do lápis é identicamente zero:
as raízes do lápis regular deixam de estar definidas. Assim, o valor-limite
das raízes existe, mas a classificação como lápis regular com par não real
desaparece continuamente no limite. Tomar `d→0` antes de extrair as raízes
descarta o lápis regular; extrair primeiro e então tomar o limite produz o
par coalescente. Os valores numéricos dos limites iterados das raízes,
enquanto elas estão definidas para `d≠0`, coincidem; a singularidade está na
classificação e na extração no ponto `d=0`, não em uma divergência dos valores.

As três primeiras detecções não são equivalentes em geral. Para
`G=diag(0,1)`, o primeiro menor principal é zero embora `G` seja
semidefinida positiva. Para `G=K=diag(1,-1)`, há uma direção negativa e as
raízes do lápis são reais. Para `G=diag(1,-1)` e
`K=[[0,1],[1,0]]`, as raízes são `±i`. No modelo de dois polos, o menor
inicial `h_s` não positivo detecta a falha principal já na ordem 1; se
`h_s<0`, já há também direção negativa nessa ordem. Se `h_s≥0`, a direção
negativa aparece na ordem 2 pelo determinante estritamente negativo (mesmo
que `h_s=0`, quando o primeiro menor já é zero). As raízes não reais aparecem
na ordem 2 para todo `d≠0`.

Isso resolve a comparação e a degeneração no modelo auxiliar. Para os jatos
sigma originais, não foi provada a decomposição em dois polos requerida por D;
por isso a ordem da primeira detecção, as raízes não reais e a não
comutatividade do limite com a extração de raízes seguem **ABERTAS**.

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
