# Lei espacial nativa em dois índices arbitrários

**PARTIAL para a positividade canônica all-order; alvo espacial E da PR #104
concluído.** A candidata antes testada em 25 pares agora é um teorema Lean
para quaisquer dois índices. A igualdade é complexa e conserva os dois
pareamentos ordenados. Não pressupõe positividade, inversibilidade de
Hankel, momentos, zeros, alturas ou uma medida espectral positiva.

Base exata: `c2c24e90b313ef090cb7e45be4f01111c7e7c650`, PR #104,
branch `agent/native-quartic-first-correction`. Branch desta investigação:
`agent/native-all-order-spatial-correction`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.
A entrega é uma PR draft empilhada sobre #104, sem merge automático.

## A — O que já estava demonstrado

A PR #41 separou ortogonalização algébrica do sinal dos pivôs: a
inversibilidade permite eliminar cruzamentos anteriores, mas não torna o
residual automaticamente uma norma de Hilbert. Essa separação permanece.
Os certificados finitos H6/K6 não são usados nesta prova all-order espacial.

A PR #104 já provou o valor do resto analítico da mesma resposta no centro,
o pareamento quártico de peso 11 igual a 55/2 e a primeira correção completa
da família J4−aJ2−bJ0. Sua seção C.1 propôs a lei espacial geral, verificada
somente em 25 pares racionais; faltava uma prova em índices arbitrários.

Reutilização de declarações reais:

- `CarryStencilBoundary.rawStencil`, `staticStencil`,
  `radialJetCoefficients`, `raw_stencil_apply`,
  `radial_jet_original_source`, `raw_stencil_complement` e
  `radial_jet_synthesis`, no ancestral `Stencil.lean`.
- `CarryNativeTfvd.coefficientWeight`, `coefficient_weight_apply`:
  multiplicação literal dos coeficientes pelo peso de endereço.
- `CarryCriticalTfvd.sectorKernel`, `field_scale_input`,
  `monomialWeight`, em `PhysicalKernels.lean` e `ResponseTaylor.lean`.
- `inner_completedNativeChiralCauchyFeature`: métrica original
  `⟨φ_i,φ_j⟩=1/(i+j+2)`.
- `CarrySelfAdjointOperator.ProjectiveDepth.pow_eq_sum_stirlingSecond_descFactorial`,
  em `NewtonStirlingTransport.lean`: usa-se sua identidade combinatória
  finita, sem identificar profundidade, endereço e ordem de jet.
- Mathlib: `fwdDiff_iter_choose_zero`, `fwdDiff_iter_comp_add`,
  `fwdDiff_iter_eq_sum_shift`, recorrências de `Nat.stirlingSecond` e
  `geom_sum₂_mul`.

Não foram alterados os módulos históricos, os repositórios consultados,
as definições materiais, a métrica ou os pins.

## B — O que foi demonstrado agora

Todos os nomes novos abaixo pertencem a `CarrySpatialCorrection`.
Os auxiliares combinatórios não definem outra sequência de momentos.

### B.1 — Identidade de diferenças finitas

Em `DifferencePowers.lean`, define-se apenas para a extração algébrica

\[
\beta_{m,p}=\frac{1}{m!}\Delta_1^m(x\mapsto x^p)(1).
\]

`difference_power_stirling` prova, para quaisquer m,p naturais,

\[
\boxed{\beta_{m,p}=S(p+1,m+1).}
\]

`power_newton_expansion` reutiliza a identidade Newton/Stirling existente;
`choose_difference_one` prova que a avaliação em 1 retém exatamente as
duas posições adjacentes na base binomial. Disso seguem:

\[
\beta_{m,p}=0\ (p<m),\quad \beta_{m,m}=1,\quad
\beta_{m,m+1}=s_m,\quad \beta_{m,m+2}=t_m,
\]

\[
s_m=\frac{(m+1)(m+2)}2,\qquad
 t_m=\frac{(m+1)(m+2)(m+3)(3m+4)}{24}.
\]

Teoremas: `difference_power_below`, `difference_power_diagonal`,
`difference_power_one_above`, `stirling_two_above`,
`difference_power_two_above`, `difference_power_sum`.

### B.2 — Os dois pareamentos se encontram numa diferença dividida

Escreva K_p(c,d) para a definição **existente**
`sectorKernel false eta h0 h1 (monomialWeight p) c d`.
O parâmetro satisfaz as condições originais `0<eta<1`; o setor false não
aplica um novo Green ao vetor. Não se presume simetria de K_p.

`raw_kernel_sum` primeiro expande o pareamento das duas sínteses completas
no produto interno Cauchy original. `static_kernel_sum` conserva os dois
fatoriais. Para p ímpar, `static_odd_divided` prova

\[
K_p(d_m,d_n)+K_p(d_n,d_m)
=\sum_{\ell=0}^{p-1}(-1)^\ell
  \beta_{m,p-1-\ell}\beta_{n,\ell},\qquad
 d_m=\operatorname{staticStencil}(m).
\]

A prova usa a igualdade complexa

\[
\frac{x^p+y^p}{x+y}
=\sum_{\ell=0}^{p-1}(-1)^\ell x^{p-1-\ell}y^\ell.
\]

Ela se aplica a x=i+1,y=j+1; o denominador é provadamente não nulo.
O segundo pareamento é reindexado, preservado e somado ao primeiro.
Não se troca cada termo por metade da soma, nem se toma parte real antes
da identidade. Os cruzamentos são calculados antes da leitura escalar.

### B.3 — Lei espacial em duas ordens independentes

O perfil `nativeEvenProfile r` é exatamente

\[
q_r=(-1)^r d_{2r}.
\]

`radial_even_calibration`, em `Regression.lean`, prova sua proveniência:

\[
\operatorname{radialJetCoefficients}(k,2r)
=(k+1)^{2r}q_r.
\]

A igualdade conserva a fase do passo imaginário original. Em conjunto com
o teorema preexistente `radial_jet_original_source`, ela identifica a
mesma entrada dos dois canais completados; não fabrica vetores por Gram
ou Cholesky. Atenção ao sinal histórico: `native_profile_zero` prova
q0=−`seedInput`; q1=`curvatureInput`; q2=`fourthShape`.

`native_odd_divided` e `native_odd_stirling` dão, em toda ordem ímpar,

\[
\boxed{
K_p(q_r,q_s)+K_p(q_s,q_r)
=(-1)^{r+s}\sum_{\ell=0}^{p-1}(-1)^\ell
 S(p-\ell,2r+1)S(\ell+1,2s+1).
}
\]

Com m=2r,n=2s e

\[
 A_{m,n}=t_m+t_n-s_ms_n,
\]

`native_first_correction` demonstra o alvo principal:

\[
\boxed{
K_{m+n+3}(q_r,q_s)+K_{m+n+3}(q_s,q_r)
=(-1)^{r+s}A_{m,n}.
}
\]

Não existe limite finito imposto a r ou s. `divided_first_correction`
mostra por que só três termos sobrevivem: ℓ=n,n+1,n+2.
As contribuições são t_m, −s_ms_n e t_n.

`native_below` prova cancelamento de todos os pesos ímpares p<m+n+1;
`native_leading` prova que a soma no peso m+n+1 é (−1)^(r+s).
`spatial_correction_diagonal` prova

\[
 A_{m,m}=\frac{(m+1)(m+2)(2m+3)}6.
\]

### B.4 — Regressão e auditoria

`quartic_weight11_regression` recupera o 55/2 anterior pela lei universal.
`correction_table` certifica exatamente as entradas

\[
(A_{2r,2s})_{r,s=0}^2=
\begin{pmatrix}1&20&126\\20&14&75\\126&75&55\end{pmatrix}.
\]

São 31 teoremas e seis definições, em quatro módulos de prova.
`Audit.lean` imprime os axiomas de todas as 37 raízes públicas e percorre
5.109 dependências de tipos e corpos. Todas são auditadas como espaciais:
os momentos canônicos e a característica completada são proibidos nessa
cadeia. Só são permitidos `propext`, `Classical.choice` e `Quot.sound`.
Não há novos axiomas matemáticos ou admissões.

## C — O que foi refutado

`correction_table_negative_direction` prova a igualdade exata

\[
(20,-1)\begin{pmatrix}1&20\\20&14\end{pmatrix}(20,-1)^T=-386.
\]

Portanto, essa tabela de coeficientes, apesar das entradas positivas, não
é uma Gram positiva. Não pode fornecer uma prova de sinal por si só.
O teste é da tabela A; não é um pivô canônico negativo e não refuta outras
realizações da geometria. Nenhuma métrica foi modificada para contorná-lo.

## D — O que permanece aberto

O resultado elimina a conjectura combinatória espacial da PR #104.
Ainda não prova uma expansão all-order da energia completada, nem o sinal
da primeira correção, nem positividade das Hankel canônicas.

A igualdade all-order da tabela não substitui a análise do resto da
resposta, a recomposição Green/bulk/bordo e as condições de não anulação
da característica nos endereços do prefixo. Esses dados não foram apagados:
eles pertencem à próxima passagem da identidade espacial ao balanço
completado. Aqui não se reivindica um transporte isométrico da forma
assinada completa para uma norma positiva.

Também não se demonstraram uniformidade na ordem, passagem simultânea
k,d→∞, controle de cauda independente de d ou positividade de todos os
residuais de Schur. Os índices r,s são arbitrários na identidade finita;
isso é distinto de um limite de fontes de suporte infinito.

## E — Próximo passo mínimo

Para d arbitrário FIXO e coeficientes reais c_r, usar a soma literal das
entradas já existentes

\[
 f_k=\sum_{r=0}^d c_r\operatorname{radialJetCoefficients}(k,2r).
\]

Transportar a lei agora provada ao **mesmo** `CarryCriticalTfvd.fullEnergy`
por `full_response_flux`, com o Taylor da resposta nativa até grau 4d+3,
resto analítico retido e não anulação eventual em cada prefixo finito.
O alvo concreto seguinte, ainda NÃO provado nesta PR, é

\[
\boxed{
(k+1)^2\left(\operatorname{fullEnergy}(k,f_k)
  -\sum_{r,s=0}^d c_rc_s h_{r+s}\right)
\longrightarrow
-\sum_{r,s=0}^d c_rc_s A_{2r,2s}h_{r+s+1}.
}
\]

Para d=2,c=(−b,−a,1), a expressão à direita reproduz
−55h5+150a h4−14a²h3+252b h3−40ab h2−b²h1, já provada na PR #104.
A prova geral deve conservar o mesmo resto e os termos mistos até a
recomposição. Não exige antecipadamente um pivô positivo.

Depois dessa passagem, determinar o sinal exigirá uma propriedade
independente da fonte; a identidade espacial não oferece tal sinal.
Este é um avanço all-order da extração, com a obrigação de sinal
precisamente separada, conforme a distinção da PR #41.

### Reprodução e evidências

Na máquina `llm`, em uma worktree desta branch com `.lake` apontando ao
ambiente original:

```bash
cd research/native-all-order-spatial-correction
python3 validate.py
```

O comando padrão recompila os 27 ancestrais de suas fontes na base exata.
`python3 validate.py --reuse-upstream` só reutiliza um bootstrap registrado
quando os hashes de TODAS as fontes e dos `.olean` coincidem. Os cinco
módulos novos, incluindo Audit, são sempre compilados explicitamente com
`lean -DwarningAsError=true`; os módulos de pesquisa não são alvos
automáticos do build raiz.

Os **15 checks locais passaram com código de saída zero**.
A validação inclui ainda `lake build --wfail` no operador e no repositório
principal, auditorias Foundation/Geometry/Analysis, comparação com a base,
verificação de fontes, pins e trabalhos antigos. As evidências estão em
`evidence/validation.json`, `evidence/lean-Audit.log`,
`evidence/upstream.json`, `evidence/source-provenance.json` e
`evidence/preservation.json`. O manifesto SHA256 cobre os arquivos da
entrega, exceto o próprio manifesto. A aprovação local não afirma CI remoto.

**Fim do relatório — conclusão: PARTIAL; lei espacial all-order provada,
transporte da correção completa e sinal canônico all-order ainda abertos.**
