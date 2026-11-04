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

`SigmaPadeAudit.lean` audita 62 raízes públicas e percorre 59.125 constantes
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

## ABERTO — próximos checkpoints

1. **E:** deduzir convergência dos coeficientes Padé e das raízes para janelas
   da fonte sigma original, condicional ao controle do resto.
2. **F:** tratar a não comutatividade dos limites em `s` e `delta`, e as três
   noções distintas de primeira detecção.
3. **Validação numérica:** extrair os momentos apenas da característica
   completada, com dois contornos de Cauchy, e comparar com as alturas
   conhecidas sem usá-las como entrada.

Até fechar E, a pergunta sobre convergência dos polos da fonte original
continua condicional. O checkpoint B estabelece a identidade algébrica entre o
pencil original e o Padé da geradora dos seus jatos; D não afirma que as
hipóteses de continuação sejam verdadeiras para esse caso.
