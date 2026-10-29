# Comutador cúbico nativo: numerador, cruzamentos e margem quadrática

**PARTIAL para a positividade canônica all-order. A obrigação do numerador
cúbico está fechada.** O pareamento foi transportado em dois argumentos
independentes e testado na família original `J₄−aJ₂−bJ₀`, com parâmetros livres.
Além disso, uma desigualdade física nova dá sinal estrito ao coeficiente
cúbico da direção quadrática, sem premissa de sinal de momentos:

\[
\boxed{U_3\ge\frac{19-7\eta^2}{240}\ge\frac1{20}>0,
\qquad0<\eta<1.}
\]

Esse coeficiente é espacial. A soma completada não linear e os residuais de
Schur continuam tendo obrigações próprias; a margem acima não os substitui.

Base exata: `ed761167d7dcb47949d510dd6d5a9cc97d27a75d`, head da PR #99,
branch `agent/native-all-order-stencil-boundary`. Continuação em
`agent/native-cubic-tfvd-numerator`, destinada à PR #99, sem merge automático.
Main: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

Usamos as mesmas colunas `φ_j=completedNativeChiralCauchyFeature j`, a síntese
Cauchy física S, o multiplicador M, seu complemento C e o Green original:

\[
M=\texttt{physicalRadialAdvance},\quad C=I-M,\quad
R_\eta=(I-\eta M)^{-1},\quad G_\eta=\eta M R_\eta^2.
\]

O domínio das identidades com resolvente é `0<η<1`. Endereço j, ordem de jet
e índice radial k continuam distintos. O passo radial original é
`δ_k=canonicalCompletedC3RadialSecondStep k=i/(k+1)`.

Reutilizamos:

- PR #92: `coefficientWeight`, `completionCommutator`,
  `completion_commutator_succ`, síntese dos coeficientes e TFVD com dois traços.
- PR #95: o peso original `monomialWeight 3 j=(j+1)^3`, os campos
  `sectorField` e `sectorKernel`, sua linearidade e `curvatureInput`.
- PR #96: `physicalCurvature`, `baseGradient`, `transportedGradient`,
  `green_inner_transport`, `curvature_resolvent_advance`,
  `gradient_pairing` e `native_gradient_norm_lower`.
- PR #98: `synthesis_shift`, `green_inner_right_numerator` e
  `double_advance_pairing`, que evitam uma inversa não limitada de M.
- PR #99: `radialJetCoefficients`, `radialLeadingScalar`,
  `radial_jet_original_source`, `radial_jet_synthesis` e os dois traços dos jets.

O theorem de norma anterior dá
`‖Rη(φ₁−φ₂)‖²≥1/60` na métrica Cauchy original. Essa norma não é fornecida
pelos momentos canônicos nem por uma fatoração de sua Hankel.

## B — O que foi demonstrado agora

### B.1 — Numerador cúbico para qualquer suporte finito

Defina os polinômios determinados pelas diferenças literais do peso p₃:

\[
p_3(j)=(j+1)^3,\quad A(j)=3j^2+3j+1,\quad B(j)=3j^2+9j+7.
\]

São `cubicForwardWeight` e `cubicBackwardWeight`. Com o mesmo
`coefficientWeight`, `cubic_commutator_succ` demonstra

\[
(C_\eta[p_3]c)_{j+1}
=\eta^{-1}A(j+2)c_{j+2}-\eta B(j)c_j.
\]

`cubic_shift_numerator` prova a igualdade inteira dos coeficientes:

\[
\boxed{
\sigma C_\eta[p_3]c
=\eta^{-1}(W_Ac-c_0e_0-7c_1e_1)-\eta\sigma^2W_Bc.
}
\]

σ é o shift unilateral existente. O fator 7 é `A(1)`, não uma nova
normalização. O primeiro traço vem de `A(0)=1`.

`cubic_physical_numerator` transporta essa igualdade antes de qualquer pairing:

\[
\boxed{
MS(C_\eta[p_3]c)
=\eta^{-1}(SW_Ac-T_3c)-\eta M^2SW_Bc,
\quad T_3c=c_0\phi_0+7c_1\phi_1.
}
\]

`cubicTrace` é somente esse readout vetorial dos traços originais. Nenhum
operador diferencial infinito ou hipótese de domínio adicional é introduzido.
A identidade algébrica vale para todo η real, com inversão total do Lean;
o uso do Green limitado abaixo mantém explicitamente `0<η<1`.

### B.2 — Transporte no Green original, em dois argumentos independentes

`cubicKernel` é um alias de
`sectorKernel true eta ... (monomialWeight 3)` da PR #95.
`cubic_kernel_original` registra o pareamento literal

\[
K_3(c,d)=\langle Sc,G_\eta S(C_\eta[p_3]d)\rangle.
\]

`cubic_green_polarized` prova, sem identificar c e d:

\[
\boxed{
\begin{aligned}
K_3(c,d)={}&\langle R_\eta Sc,R_\eta SW_Ad\rangle
-\langle R_\eta Sc,R_\eta T_3d\rangle\\
&-\eta^2\langle R_\eta MSc,R_\eta MSW_Bd\rangle.
\end{aligned}
}
\]

Os estados ponderados permanecem nos pareamentos mistos. Não se presume
que possam ser substituídos por normas. Só depois a parte real diagonal é
extraída em `cubic_green_diagonal`.

### B.3 — Confronto com J₄−aJ₂−bJ₀ e os cruzamentos

`criticalFamily k a b` usa os coeficientes originais dos jets radiais:

\[
c=c_{k,4}-a c_{k,2}-b c_{k,0},\qquad a,b\in\mathbb R.
\]

`critical_family_original_source` demonstra a igualdade no par de canais
completados com `projectiveChiralDifferenceJet k 4 − a J₂ − b J₀`.
As fases e os fatoriais permanecem nos c. Não se escolhem a,b por um sinal
de momento ou por uma Gram auxiliar.

Escrevendo `γ₄=radialLeadingScalar k 4` e `γ₂=radialLeadingScalar k 2`,
`critical_family_synthesis` identifica

\[
Sc=\gamma_4C^4\phi_0-a\gamma_2C^2\phi_0-b\phi_0.
\]

`critical_family_explicit` prova a entrada concreta de cinco endereços:

| j | c_j | A(j) | B(j) |
| --- | --- | --- | --- |
| 0 | γ₄−aγ₂−b | 1 | 7 |
| 1 | −4γ₄+2aγ₂ | 7 | 19 |
| 2 | 6γ₄−aγ₂ | 19 | 37 |
| 3 | −4γ₄ | 37 | 61 |
| 4 | γ₄ | 61 | 91 |

`critical_family_two_traces` e `critical_family_cubic_trace` conservam

\[
T_3c=(\gamma_4-a\gamma_2-b)\phi_0
+(-28\gamma_4+14a\gamma_2)\phi_1.
\]

`critical_family_support` prova suporte nos endereços 0…4;
`critical_cubic_commutator_support` conserva o halo 0…5 do comutador.
Pela fórmula literal do comutador e pela entrada anterior, o coeficiente no
endereço 5 é `−91ηγ₄`. Ele não é apagado ao sintetizar a entrada original.

Denote por `Krs=K₃(c_{k,r},c_{k,s})`. Os teoremas
`cubic_three_input_expansion` e `critical_cubic_expansion` dão

\[
\boxed{
\begin{aligned}
\Re K_3(c,c)={}&\Re K_{44}+a^2\Re K_{22}+b^2\Re K_{00}\\
&-a\Re(K_{42}+K_{24})-b\Re(K_{40}+K_{04})
+ab\Re(K_{20}+K_{02}).
\end{aligned}
}
\]

São os nove pareamentos ordenados originais. Não é usada uma simetria
Hermitiana que o kernel não tenha demonstrado. As igualdades de B.1 e B.2
valem para cada uma dessas entradas, com os pesos concretos da tabela.
Esta rodada não determinou o sinal da soma para a,b gerais nem resolveu
seus cancelamentos com os outros setores da resposta completada.

### B.4 — Nova orientação física do sinal na direção quadrática

Na entrada original `q=curvatureInput=(-1/2,1,-1/2)`, a mesma fonte cúbica
produz o polinômio físico

\[
\mathsf B_2=7I-38M+37M^2
\quad(\texttt{cubicQuadraticMultiplier}).
\]

Esse é um polinômio espacial forçado pelo cálculo. Não é o operador do canal
retornado. `cubicTangent` reescreve o comutador sobre essa direção:

\[
t_{3,\eta}(f)=-\frac{19}{2\eta}Mf+
\frac\eta2 M\mathsf B_2f.
\]

`cubic_native_tangent` identifica `t₃,η(φ₀)=S(Cη[p₃]q)` antes de aplicar
qualquer desigualdade. Em particular, os endereços 1,2,3 do vetor são

\[
\left(-\frac{19}{2\eta}+\frac{7\eta}{2},\ -19\eta,\ \frac{37\eta}{2}\right).
\]

Com `d_f=physicalCurvature f` e `v_f=RηMCf`,
`cubic_curvature_polarized` prova primeiro

\[
\boxed{
\langle d_f,G_\eta t_{3,\eta}(g)\rangle
=\tfrac14\left(19\langle v_f,v_g\rangle
-\eta^2\langle v_f,\mathsf B_2v_g\rangle\right).
}
\]

`cubic_curvature_diagonal` toma a diagonal real. O pareamento com
\(\mathsf B_2\) permanece, incluindo suas partes assinadas. Seu símbolo
`7−38u+37u²` pode ser negativo. Não é pressuposta sua positividade.

A desigualdade independente da fonte vem do complemento exato:

\[
7I-\mathsf B_2=M(38I-37M),\qquad u(38-37u)\ge0\quad(0\le u\le1).
\]

`cubic_multiplier_upper_positive` e `cubic_multiplier_inner_upper` provam
`\mathsf B₂≼7I` na métrica física original. Portanto,
`cubic_curvature_lower` dá

\[
\Re\langle d_f,G_\eta t_{3,\eta}(f)\rangle
\ge\frac{19-7\eta^2}{4}\|v_f\|^2.
\]

`nativeU3` é o coeficiente `spatialU true ... (monomialWeight 3)` já definido
na PR #95. Sua identificação com o pareamento anterior é provada em
`native_cubic_identification`. A norma original `‖v_{φ₀}‖²≥1/60` dá

\[
\boxed{U_3\ge\frac{19-7\eta^2}{240}\ge\frac1{20}>0.}
\]

São `native_cubic_lower_bound`, `native_cubic_uniform_lower` e
`native_cubic_pos`. As constantes 19,7,38,37 vêm dos pesos cúbicos e do stencil;
240 é `4×60`. Não há ajuste de fonte, normalização ou métrica.

## C — Obstruções e distinções preservadas

`cubic_seed_negative` prova no mesmo kernel

\[
\boxed{\Re K_3(e_0,e_0)<0\qquad(0<\eta<1).}
\]

O comutador literal é `Cη[p₃]e₀=−7ηe₁`; seu sinal vem do cruzamento Green
positivo já demonstrado na fonte. Assim, o kernel cúbico não é uma forma
positiva em todas as entradas finitas. A orientação quadrática de B.4 não
autoriza apagar a direção-semente ou seus cruzamentos na família de B.3.

O resultado novo é sobre um coeficiente espacial da resposta. O termo cúbico
aparece com sua própria contribuição assinada na expansão da resposta da
PR #95. Sinal positivo de U₃ não determina sozinho o sinal da soma física.
Também não é uma margem relativa fixa entre os canais incidente e retornado.
Os NO-GOs anteriores para essa margem permanecem válidos.

Nenhuma positividade Hankel all-order, positividade do novo residual canônico
ou identificação de uma Gram auxiliar com o kernel canônico é anunciada.
Os certificados finitos anteriores permanecem válidos.

## D — Auditoria e reprodução

São 31 teoremas e oito definições, em `CubicNumerator.lean`, `CubicGreen.lean`,
`CriticalFamily.lean` e `QuadraticSign.lean`. As 39 raízes públicas têm
`#print axioms` e travessia dos tipos/corpos:

- Espacial: 38 raízes, 5.149 dependências; proíbe a sequência canônica,
  a característica completada e os consumidores de sinal selecionados.
- Proveniência: `critical_family_original_source`, com 5.274 dependências;
  permite a característica que faz parte da fonte completada original,
  mas proíbe momentos e consumidores de positividade.

As contagens se sobrepõem. Ambos os grupos permitem somente `propext`,
`Classical.choice` e `Quot.sound`. As novas provas de sinal estão no grupo
espacial, sem a característica e sem momentos como dependências.
Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos novos.

`validate.py` recompila os 26 ancestrais de pesquisa efetivamente importados
e compara os hashes com a base. Compila explicitamente os quatro módulos e
a auditoria com warnings como erros; executa `lake build --wfail`,
Foundation/Geometry/Analysis e a preservação da base, fontes e trabalhos antigos.
Os comandos e códigos de saída estão em `evidence/validation.json`.
O manifesto acompanha as fontes e os logs; a raiz Lake sozinha não compila
os módulos novos de pesquisa.
Nesta execução, **os 15 comandos passaram com código de saída zero**, assim
como as verificações de preservação das fontes, pins, main e trabalhos antigos.
`sha256sum -c MANIFEST.sha256` permite conferir os arquivos entregues.

Para recriar a worktree no servidor `llm` após a remoção:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-cubic-tfvd-numerator \
  agent/native-cubic-tfvd-numerator
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-cubic-tfvd-numerator/.lake
```

Na pasta `research/native-cubic-tfvd-numerator` dessa worktree:

```bash
python3 validate.py
```

## E — Próxima obrigação mínima

O numerador cúbico geral e os nove cruzamentos da entrada livre estão
identificados. A margem da direção quadrática está demonstrada. O primeiro
passo curto ainda não provado é uma calibração cúbica igualmente concreta
para o stencil quártico original, antes de tentar sinais da combinação geral.

Para `d₄=fourthShape` e `w₄=RηMC²φ₀`, confrontar no mesmo Green a candidata

\[
\boxed{
\Re K_3(d_4,d_4)\stackrel{?}=
\frac1{576}\Re\langle w_4,
\big[27I+26C+61C^2-\eta^2C^2(36I-120C+91C^2)\big]w_4\rangle.
}
\]

Esses polinômios vêm dos pesos A,B da tabela, reescritos em `C=I−M`.
A igualdade e uma eventual cota do lado direito não foram formalizadas
nesta entrega. A primeira obrigação é a identidade com o mesmo comutador,
incluindo seu halo; não é permitido substituir o kernel pelo lado positivo.

Depois, controlar os cruzamentos K₄₂,K₂₄,K₄₀,K₀₄,K₂₀,K₀₂ e os cancelamentos
com os demais setores da resposta completada. A lei Taylor e seu resto
precisam alcançar a ordem suficiente para a parte finita da combinação J₄−aJ₂−bJ₀.
Só então a identificação do residual de Schur da PR #41 pode orientar
uma desigualdade da fonte para esse residual completo.

Entrega em PR draft sobre a PR #99, sem merge automático. Main, fontes,
amplitudes, pesos, métrica, pins e trabalhos anteriores permanecem preservados.
O relatório completo, logs e manifesto são copiados localmente e conferidos
antes de remover apenas a worktree temporária desta tarefa.

**Fim do relatório.**
