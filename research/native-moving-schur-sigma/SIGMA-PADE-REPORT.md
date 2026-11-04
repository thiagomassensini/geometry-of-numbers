# Missão Luna — pencil sigma assinado e correspondência de Padé

**Estado da missão: em andamento.** Os checkpoints A e B estão provados em
Lean, compilados com `-DwarningAsError=true`, auditados transitivamente e
publicados. Os checkpoints C–F, a validação numérica e o relatório final ainda
estão abertos.

## Proveniência e Git

Branch: `agent/native-sigma-pade-signed-pencil`.

SHA da base ao iniciar: `9c74f14195410a9221448917ae469f71b9dcfe0b`, igual ao
remoto `agent/native-raw-rank-one-deflation`. O worktree desta missão foi
criado independentemente nessa base. O checkout auxiliar Carry está sujo com
alterações preexistentes não relacionadas; elas foram preservadas.

- Checkpoint A: [commit `189de259`](https://github.com/thiagomassensini/geometry-of-numbers/commit/189de2599a84aa78e6a5b50b71d5aa0b9a4645b9).
- Checkpoint B: [commit `b2998c59`](https://github.com/thiagomassensini/geometry-of-numbers/commit/b2998c595df575e95de664085a083616ba094eec).
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

`SigmaPadeAudit.lean` audita 35 raízes públicas e percorre 35.014 constantes
alcançáveis nos tipos e corpos. Foram aceitos somente os axiomas-base do Lean
`[propext, Classical.choice, Quot.sound]`. A auditoria exige como dependências
`sigmaMatrix`, `completedSigmaLogJet` e
`completedNativeOperatorCharacteristic`, confirmando a proveniência original.

```bash
cd /home/thlinux/worktrees/geometry-of-numbers-native-sigma-pade-signed-pencil
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaSignedPencil
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeCorrespondence
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeAudit
```

O script usa os caches Lean históricos e permite configurar
`SIGMA_REFERENCE_ROOT` e `CARRY_LEAN_ROOT`. O diretório de cache local
`.cache/` não é versionado e foi preservado.

## ABERTO — próximos checkpoints

1. **C:** formalizar o par auxiliar
   `h_n = m Re((gamma+i delta)^(-2(n+1)))`, sua direção negativa, o polinômio
   do pencil e a recuperação algébrica `gamma ± i delta`. O par ainda não foi
   identificado como contribuição da fonte original.
2. **D:** separar, sob hipóteses analíticas explícitas, o fator de um zero
   simples da característica original e obter um resto
   `|r_n| ≤ C eta^n`, com `eta < |zeta|`.
3. **E:** deduzir convergência dos coeficientes Padé e das raízes para janelas
   da fonte sigma original, condicional ao controle do resto.
4. **F:** tratar a não comutatividade dos limites em `s` e `delta`, e as três
   noções distintas de primeira detecção.
5. **Validação numérica:** extrair os momentos apenas da característica
   completada, com dois contornos de Cauchy, e comparar com as alturas
   conhecidas sem usá-las como entrada.

Até fechar D/E, a pergunta sobre convergência dos polos da fonte original
continua sem resposta incondicional. O checkpoint B estabelece somente a
identidade algébrica entre o pencil original e o Padé da geradora dos seus
jets.
