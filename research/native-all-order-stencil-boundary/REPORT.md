# Stencils nativos e bordo físico em ordem arbitrária

**PARTIAL para a positividade canônica all-order. A obrigação da PR #98 está
fechada.** Os pesos originais dos jets, com fase e fatorial, foram identificados
com potências do complemento físico. O polinômio de bordo da PR #97 agora tem
uma calibração operatorial exata. Dessa identidade foi deduzida a não
negatividade do coeficiente espacial linear dos jets em toda ordem m≥2.

Essa lei espacial não é uma prova da positividade Hankel, da positividade
estrita em toda ordem, ou do sinal do residual completado após os cancelamentos.

Base: `a020c1f0165cf5ff80100d5508ce42d7d5ab8f1d`, head da PR #98,
branch `agent/native-linear-tfvd-traces`. Continuação em
`agent/native-all-order-stencil-boundary`, sobre a PR #98, sem merge automático.
Main: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

Mantemos o carrier Cauchy físico original, as colunas
`φ_j=completedNativeChiralCauchyFeature j`, a síntese
`S=physicalCauchySynthesis` e os operadores existentes

\[
M=\texttt{physicalRadialAdvance},\quad C=I-M,\quad
R_\eta=(I-\eta M)^{-1},\quad G_\eta=\eta M R_\eta^2.
\]

As leituras com Green limitado usam `0<η<1`. C e M são contrativos e positivos
na métrica original. `physicalRadialAdvance_injective`, de
`NativeGeometricLogClock.lean`, fornece somente a injetividade de M;
não se constrói uma inversa não limitada de M.

Reutilizamos diretamente:

- `CompletedGreenForwardDifferenceLimit.lean`: `completedGreenForwardWeight`,
  os pesos binomiais assinados originais.
- `CompletedNativeProjectiveChiralForwardDifference.lean`:
  `projectiveChiralDifferenceJet`, incluindo o fator radial e fatorial original.
- PR #95: `monomialWeight`, `criticalInput`, `second_scale` e a realização
  original da direção quadrática.
- PR #96: `physicalCurvature`, `physicalTangent`,
  `curvature_green_nonnegative`, `green_inner_transport`,
  `fourthShape` e `fourth_tangent_defect`.
- PR #97: `boundaryPolynomial`, suas identidades em toda ordem e os
  certificados estritos do bordo e do coeficiente espacial quárticos.
- PR #98: `physical_linear_numerator`, a igualdade com os dois traços
  para qualquer entrada finitamente suportada.

Usar a síntese Cauchy não identifica sua norma com a norma da torre. Essa
síntese é a existente, com sua métrica não diagonal. As quadraturas reais e a
construção dos dois canais completados são preservadas pelas pontes anteriores.

## B — O que foi demonstrado agora

### B.1 — Coeficientes originais e proveniência dos dois canais

Os quatro objetos de `Stencil.lean` são abreviações explícitas das somas
originais, não vetores obtidos por fatoração de momentos. Escreva

\[
w_{m,j}=(-1)^{m-j}\binom mj,
\quad a_m=\sum_{j=0}^m w_{m,j}e_j,
\quad d_m=\frac1{m!}a_m,
\]

\[
\delta_k=\texttt{canonicalCompletedC3RadialSecondStep}\ k
=\frac{i}{k+1},\qquad
c_{k,m}=\frac1{m!\,\delta_k^m}a_m,
\quad s_{k,m}=\frac{(-1)^m}{m!\,\delta_k^m}.
\]

São `rawStencil`, `staticStencil`, `radialJetCoefficients` e
`radialLeadingScalar`. O índice k é o da regularização radial; não é
profundidade Carry ou endereço material. m é ordem de diferença.

`raw_stencil_apply`, `raw_stencil_zero`, `raw_stencil_one` e
`radial_jet_two_traces` demonstram os coeficientes literais, em particular

\[
\boxed{(c_{k,m})_0=s_{k,m},\qquad
(c_{k,m})_1=-m s_{k,m}.}
\]

`radial_leading_nonzero` prova `s_{k,m}≠0`. Nenhuma fase é substituída por
um valor absoluto. O fatorial e o passo imaginário permanecem nas definições.

`radial_jet_original_source` prova a igualdade vetorial no par de canais:

\[
\boxed{
\texttt{physicalCompletedFiniteSource}\ k\ c_{k,m}
=\texttt{projectiveChiralDifferenceJet}\ k\ m.
}
\]

Esse theorem usa os coeficientes nas duas pernas da fonte completada original.
O produto de duas energias ou uma resposta escalar não é usado para identificar
os estados. As amplitudes e os pesos quirais continuam nas definições antigas.

### B.2 — Calibração com o complemento original

`advance_power_feature` e `negative_unit_power` permitem aplicar o binômio
no anel dos operadores limitados, sem supor comutatividade desse anel inteiro.
Somente M e a unidade escalar precisam comutar.

`raw_stencil_binomial`, `raw_stencil_complement` e `radial_jet_synthesis` provam

\[
Sa_m=(M-I)^m\phi_0=(-1)^mC^m\phi_0,
\qquad
\boxed{Sc_{k,m}=s_{k,m}C^m\phi_0.}
\]

O lado esquerdo usa os pesos nativos anteriores. O lado direito é uma
identidade demonstrada depois; não foi usado para defini-los.

S é a síntese Cauchy dos coeficientes. A síntese completada nos dois canais,
na igualdade de B.1, é outra aplicação existente. As duas igualdades usam o
mesmo c, mas não afirmam que essas aplicações sejam iguais ou isométricas.

### B.3 — O polinômio de bordo agora é um operador físico identificado

Reutilizando exatamente os P da PR #97,

\[
P_0(x)=0,\qquad P_{n+1}(x)=n+2+xP_n(x),
\]

`boundarySymbol` avalia essa recorrência no contínuo original e
`boundaryOperator` aplica `intervalMultiplier`. O theorem
`boundary_symbol_eval` identifica o símbolo com `P_n(1-u)`. Os teoremas
`boundary_operator_zero` e `boundary_operator_succ` provam

\[
\mathsf P_0=0,\qquad \mathsf P_{n+1}=(n+2)I+C\mathsf P_n.
\]

Portanto, `\mathsf P_n=P_n(C)` está calibrado pelo multiplicador original;
não há coeficientes livres. `boundary_operator_identity` fecha a igualdade
proposta no relatório anterior, no espaço inteiro:

\[
\boxed{
M^2\mathsf P_n=C^{n+2}-I+(n+2)M-M^2C^n.
}
\]

`boundary_operator_positive`, `boundary_operator_lower_positive` e
`boundary_operator_lower` deduzem

\[
\mathsf P_n\succeq0,\quad \mathsf P_{n+1}\succeq(n+2)I.
\]

`boundary_product_positive` também prova, para todo m,n,

\[
\boxed{C^m\mathsf P_n\succeq0.}
\]

Seu símbolo é `(1-u)^m P_n(1-u)≥0` no intervalo físico. Essa positividade
é demonstrada no espaço L² original, sem trocar a métrica ou fornecer um
predicado equivalente à positividade dos momentos como hipótese.

### B.4 — Defeito nativo inteiro em toda ordem m=n+2

Defina expressões nos mesmos operadores:

\[
f_{k,n}=-2s_{k,n+2}C^n\phi_0,
\qquad b_{k,n}=s_{k,n+2}M\mathsf P_n\phi_0.
\]

São `nativeLift` e `nativeBoundary`. `native_lift_curvature` identifica
`physicalCurvature f_{k,n}=Sc_{k,n+2}`. Mantendo os dois traços da PR #98 e
usando a injetividade de M, `native_tangent_boundary` demonstra

\[
\boxed{
S(C_\eta[p_1]c_{k,n+2})
=t_\eta(f_{k,n})+\eta^{-1}b_{k,n}.
}
\]

Aqui p₁ é o peso original `j+1`, e `tη=physicalTangent`. A igualdade é
vetorial, para todo k,n e η real. A aplicação do resolvente mantém `0<η<1`.
O halo exterior do comutador continua no lado esquerdo original.

### B.5 — Uma lei de sinal espacial válida em toda ordem

`boundary_polarized_factor` é demonstrado para dois argumentos físicos
independentes f,g, antes de tomar parte real ou diagonal. Com
`v_f=RηMf`, ele prova

\[
\boxed{
\langle C^mf,G_\eta M\mathsf P_ng\rangle
=\eta\langle v_f,C^m\mathsf P_nv_g\rangle.
}
\]

O fator contém os mesmos cruzamentos. `boundary_pair_nonnegative` usa a
positividade calibrada de B.3. Especializando a
`f=s_{k,n+2}φ₀`, com a fase complexa original, segue
`native_boundary_pair_nonnegative`:

\[
\Re\langle Sc_{k,n+2},G_\eta b_{k,n}\rangle\ge0.
\]

Conservando esse termo na identidade completa B.4, e reutilizando o controle
de curvatura da PR #96, `native_linear_coefficient_nonnegative` conclui

\[
\boxed{
\forall k,n,\quad
\Re\langle Sc_{k,n+2},G_\eta S(C_\eta[p_1]c_{k,n+2})\rangle\ge0,
\qquad 0<\eta<1.
}
\]

Essa é uma lei não condicional de sinal para esse coeficiente espacial
linear da família nativa em todas as ordens m≥2. Não recebe sinal de h,
pivô ou Hankel, e não usa tabelas de zeros, alturas ou quadratura theta.

### B.6 — Regressões exatas, incluindo as fases

`Regression.lean` prova:

- `raw_stencil_two` e `radial_second_regression`: a entrada radial de ordem
  dois é exatamente `criticalInput k 0`, com o sinal negativo já existente.
- `static_fourth_regression`: `d₄=fourthShape`, com os pesos originais `/4!`.
- `radial_fourth_regression`: `c_{k,4}=δ_k^{-4} fourthShape`.
- `boundary_operator_two`: `\mathsf P₂=5I−2M`.
- `fourth_boundary_regression`:

\[
\boxed{b_{k,2}=\delta_k^{-4}
\left(\frac5{24}\phi_1-\frac1{12}\phi_2\right).}
\]

O bordo concreto da PR #97 é reproduzido literalmente. Seus certificados
estritos e os certificados finitos canônicos anteriores permanecem válidos.

## C — O que foi refutado ou excluído

Esta rodada não acrescenta um NO-GO da geometria. O defeito quártico da
PR #96 continua não nulo; a extensão correta o conserva como parte da família
de bordos demonstrada aqui. A tentativa de um lift sem essa correção continua
refutada para aquela realização específica.

Também continua válido o contraexemplo da PR #98:
o coeficiente linear na fonte-semente de ordem zero é negativo. O theorem
novo tem m≥2. Ele não afirma positividade em todas as entradas finitas ou nas
combinações lineares arbitrárias de jets, incluindo a direção-semente.

Ter sinal nas diagonais de uma família, mesmo em toda ordem, não identifica
os cruzamentos com uma Hankel. A identidade polarizada B.5 conserva os
cruzamentos de seu próprio kernel; sua identificação com o kernel canônico
completado não é afirmada.

## D — Alcance, auditoria e reprodução

São quarenta teoremas e oito definições em quatro módulos novos:
`Stencil.lean`, `BoundaryOperator.lean`, `NativeBoundary.lean`, `Regression.lean`.
`Audit.lean` imprime os axiomas das 48 raízes públicas e percorre tipos e corpos.

- Grupo espacial: 47 raízes, 5.210 dependências; proíbe sequência canônica,
  característica completada e consumidores de positividade selecionados.
- Grupo de proveniência: somente `radial_jet_original_source`, com 5.268
  dependências; permite a característica que já aparece na fonte completada
  original, mas proíbe momentos e consumidores de sinal.

As contagens transitivas dos grupos se sobrepõem. Ambos permitem somente
`propext`, `Classical.choice` e `Quot.sound`. O grupo espacial inclui todas as
novas provas de sinal. O grupo da fonte é uma igualdade vetorial exata, sem
premissa de positividade. Nenhum grupo usa axiomas matemáticos novos,
`sorry`, `admit` ou `native_decide`.

O resolvente limitado completo é mantido; não há truncamento de sua cauda.
As entradas de cada jet têm suporte finito e a ordem é arbitrária. Isso não
estabelece um domínio infinito para os pesos não limitados de todos os jets.
As duas pernas e suas amplitudes permanecem nas definições completadas; a
lei de sinal nova controla o coeficiente espacial indicado, sem controlar
automaticamente o balanço quiral não linear inteiro.

`validate.py` recompila os 29 ancestrais de pesquisa importados, verifica seus
hashes contra a base, compila explicitamente os cinco módulos de prova e
auditoria com warnings como erros, roda `lake build --wfail` e as auditorias
Foundation/Geometry/Analysis. A raiz Lake sozinha não inclui os módulos de
pesquisa. Os comandos, códigos de saída e tempos estão em
`evidence/validation.json`; fontes, pins e trabalhos protegidos, em
`source-provenance.json` e `preservation.json`. O manifesto acompanha a entrega.
Nesta execução, **os 15 comandos passaram com código de saída zero**, assim
como as verificações de preservação das fontes, pins, main e trabalhos antigos.
`sha256sum -c MANIFEST.sha256` permite conferir os arquivos entregues.

Para recriar a worktree após sua remoção, no servidor `llm`:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-all-order-stencil-boundary \
  agent/native-all-order-stencil-boundary
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-all-order-stencil-boundary/.lake
```

Na pasta `research/native-all-order-stencil-boundary` dessa worktree:

```bash
python3 validate.py
```

## E — Primeiro ponto aberto e próxima obrigação mínima

A identificação binomial e o bordo P da resposta linear p₁ estão fechados.
Repetir a prova de que uma Gram auxiliar é positiva não reduziria o problema.
Falta controlar a resposta original além de p₁ e o balanço completado depois
de seus cancelamentos, preservando as combinações de jets da direção crítica.
O resultado B.5 não resolve essa obrigação.

O próximo alvo curto é o numerador do **comutador cúbico original**
`p₃(j)=(j+1)^3`, que já aparece na expansão da resposta da PR #95. Para qualquer
coeficiente finito c, confrontar e formalizar a identidade candidata

\[
\boxed{
\begin{aligned}
MS(C_\eta[p_3]c)\stackrel{?}={}&
\eta^{-1}S\big((3j^2+3j+1)c_j\big)\\
&-\eta M^2S\big((3j^2+9j+7)c_j\big)
-\eta^{-1}(c_0\phi_0+7c_1\phi_1).
\end{aligned}
}
\]

Os polinômios vêm das diferenças literais de p₃. Essa igualdade não foi
formalizada nesta entrega. Deve usar o mesmo `coefficientWeight`, sem criar
um operador diferencial infinito ou assumir domínio não provado.

Depois, transportar esse numerador em dois argumentos e testá-lo nas
combinações nativas `J₄−aJ₂−bJ₀`, com a,b livres. A meta será resolver os
cruzamentos e cancelamentos entre os setores da PR #95, não postular sinal
para cada parcela ou extrapolar sinais diagonais. Só após a soma completada
se deve identificar sua parte finita com o residual de Schur da PR #41.

Não foi provada nesta rodada a positividade Hankel all-order, nem a
positividade estrita de todos os coeficientes lineares, nem uma lei de sinal
do residual canônico não linear. Foi demonstrada uma nova lei espacial
all-order da fonte original, com seu bordo e sua proveniência preservados.

Entrega em PR draft sobre a PR #98, sem merge automático. Main, fontes, pesos,
amplitudes, métrica e pins permanecem preservados. A cópia local completa,
com logs e manifesto verificados, precede a remoção apenas da worktree própria.

**Fim do relatório.**
