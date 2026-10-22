# Fase nativa e compensação confluente no Green completo

**PARTIAL.** A investigação da PR #55 obteve uma fórmula física exata para
o primeiro coeficiente potencialmente não real de χ e localizou sua
compensação no Green oculto/central/comprimido. O agrupamento compensado
possui um prolongamento confluente demonstrado, sem apagar quadraturas.

**Não foi certificado que esse coeficiente seja não nulo.** O valor
aproximado −0,284668 para sua parte imaginária é um diagnóstico de prefixos
materiais, com cauda infinita ainda não certificada. Não foi provada
positividade canônica all-order nem uma nova margem no residual da #41.

Base imutável: `77e681de19ac690ec1187899941d275e7e931267`, PR #55.
Branch: `agent/native-green-phase-compensation`.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
PR empilhada sobre a #55, sem merge automático. As PRs anteriores e a
main são preservadas; nenhuma é presumida integrada.

## A — O que já estava demonstrado

A #54 constrói a centralização da fonte f, com f(0)≠0, sem apagar o par
de forcing. A #55 prova que a mesma centralização anula também os dois
termos do primeiro componente comprimido. Usamos os nomes existentes:

- `mixed_forcing_exact`, `companion_centered_bilinear`,
  `mixed_regular_anchor`, `retained_regular_ratio`;
- `value_ratio_undressed`, `value_ratio_origin_derivative`;
- `complete_mixed_hidden_factor`, provenientes do ledger da #37;
- `exact_even_green_residual`, `exact_odd_green_residual` e o limite
  físico da #53, avaliados no polinômio exato Pₛ,ₙ da #41.

A derivada do complemento material em zero já era −i w. A estimativa
`baseTwoComplexMaterialGradient_norm_le` já dominava uniformemente a série
COMPLETA de gradientes em norma lp; a continuação holomorfa local também
já estava provada. Essa infraestrutura é reaproveitada, sem recalcular
momentos, zeros ou alturas.

Notação: Y é o estado material original com seed, interior e retorno de
células completas; Z=DY é seu dressing original; Q é o complemento central.
K é o clock original aplicado a Y(0), no domínio já demonstrado; w=QK.
α(t) é `carryMaterialClockCentralCoefficient (Y t)`; a é a escala original
h₀; f é o forcing escalar original. t,u são parâmetros materiais reais,
não profundidades verticais nem o índice radial da #53.

## B — O que foi demonstrado agora

### 1. Regularidade do mesmo estado, antes do readout

`material_gradient_analytic` transporta a continuação complexa local da
série de gradientes para a função REAL com valores no lp² original.
`material_boundary_analytic` reutiliza a igualdade já provada entre o
retorno completo e a resposta sintetizada menos o seed.

`material_state_analytic` reúne as três componentes no MESMO produto de
Hilbert. Primeiro vem o resultado vetorial; depois são aplicados os probes.
Também estão provados `dressed_state_analytic`, `companion_first_analytic`,
`compressed_first_analytic` e `companion_probe_analytic`.

Portanto há derivadas fortes de todas as ordens dessas funções de fonte.
**Isso não afirma que Y pertença a Dom(Lⁿ) em toda ordem**, não altera o
clock, e não contorna o NO-GO do Krylov material da #36. A regularidade é
obtida diretamente pela continuação da série original e pelo dressing,
não por uma suposição sobre potências de um operador não limitado.

### 2. Coeficiente quadrático extraído da fonte

Definimos apenas observações da fonte já sintetizada:

\[
\beta(t)=\langle w,QY_t\rangle,\qquad
J_2=\operatorname{dslope}_0^2Y(0),\qquad \kappa=\alpha(K).
\]

J₂ é o segundo coeficiente vetorial da própria curva analítica Y; não é
um vetor fabricado a partir dos momentos. `source_center_derivative` dá
α′(0)=−iκ e `source_overlap_derivative` conserva β′(0)=−i‖w‖².

`native_quadratic_expansion` fornece uma identidade EVENTUAL EXATA,
com resto analítico H, e não uma subtração de aproximações das energias:

\[
\chi(t)=2\|w\|^2t+t^2H(t),\qquad H(0)=\chi_2.
\]

`second_coefficient_physical` e `phase_coefficient_is_native_jet` identificam

\[
\boxed{\chi_2=2i\left(\langle w,QJ_2\rangle+\|w\|^2\kappa\right)
=\operatorname{Jet}_2\chi.}
\]

O teorema `phase_coefficient_im_physical` explicita sua parte imaginária
μ em termos dos mesmos pareamentos materiais. Em particular,
`phase_quadratic_tendsto` demonstra

\[
\frac{\chi(t)-\overline{\chi(t)}}{t^2}
\longrightarrow\chi_2-\overline{\chi_2}=2i\mu.
\]

As ordens zero e um não têm fase; a ordem dois é a primeira POSSÍVEL.
Sem provar μ≠0, não se afirma que ela seja efetivamente a primeira não nula.
Essa prova não recebe sinal de pivô, matriz Hankel positiva, altura ou
resultado numérico como entrada.

### 3. A fase é mantida no numerador completo

Seja

\[
W(t,u)=a^2tu\,\overline{f(t)}f(u),\qquad
P(t,u)=W(t,u)[\chi(t)-\overline{\chi(t)}].
\]

A é o `companionCoefficient` da #55 e M a soma dos dois cruzamentos
forcing/compressed e compressed/forcing. `mixed_confluent_numerator` prova,
onde f(t),f(u)≠0, INCLUSIVE EM t=u,

\[
\boxed{M(t,u)=(u-t)[A(t,u)+\widetilde T(t,u)]+P(t,u),}
\qquad
\widetilde T(t,u)=W(t,u)\operatorname{dslope}\chi(t,u).
\]

Na diagonal, dslope usa χ′(t). A fase P não é substituída por zero.
Somamos P ao grupo central/comprimido−oculto e retiramos o MESMO P do
cruzamento; o balanço original permanece exatamente igual.

Denotando o Green oculto por Ghid e os canais central e comprimido por
Gcen,Gcmp, o numerador compensado é

\[
G_{\rm comp}=G_{\rm cen}+G_{\rm cmp}-G_{\rm hid}+P.
\]

`compensated_source_factor` prova sua fatoração física na vizinhança da fonte:

\[
G_{\rm comp}(t,u)=(u-t)D_{\rm comp}(t,u),\qquad
D_{\rm comp}=R-A-\widetilde T.
\]

R é o `remainderCoefficient` ORIGINAL da #37/#54. Essa fórmula fixa a
extensão a partir da fonte; não define uma métrica nem pressupõe seu sinal.
`compensated_row_analytic` prova analiticidade das linhas no centro.
`compensated_diagonal_confluence` prova o limite do quociente físico para
CADA ponto da diagonal em uma vizinhança da origem. Não se usa a convenção
0⁻¹=0 como se fosse continuidade.

`native_phase_diagonal_compensation` identifica a localização física exata:

\[
\boxed{P(t,t)=G_{\rm hid}(t,t)-G_{\rm cen}(t,t)-G_{\rm cmp}(t,t).}
\]

`phase_residue_fourth_order` acrescenta a escala e o coeficiente:

\[
\frac{P(t,t)}{t^4}\longrightarrow
 a^2\overline{f(0)}f(0)(\chi_2-\overline{\chi_2}).
\]

Esse limite diz respeito ao numerador material na diagonal; não é uma nova
lei radial para as energias individuais da #42/#53.

### 4. Dois índices e retorno aos coeficientes canônicos

`native_ratio_kernel_jet` transporta DOIS índices independentes:

\[
\operatorname{Jet}_{p,q}(\operatorname{dslope}\chi)
=\operatorname{Jet}_{p+q+1}\chi.
\]

Os coeficientes (1,0) e (0,1) são ambos χ₂. São coeficientes de um CANAL do
ledger; não são declarados iguais aos momentos canônicos h.

Após a centralização original, A continua cancelando exatamente.
`centered_confluent_balance` demonstra, para famílias complexas independentes,

\[
\widetilde T[c,d]+D_{\rm comp}[\widehat c,\widehat d]
=\mathcal B[c,d].
\]

`canonical_confluent_pullback` conserva todos os fatores literais e chega
novamente ao MESMO residual canônico Rₛ da #54. Não há substituição de
momento, primeira coluna, métrica, estado, dressing ou retorno.
A identificação com Pₛ,ₙ da #41 permanece a anterior; não foi provada uma
nova margem positiva ao avaliar os dois termos da nova decomposição.

## C — Obstruções e controles

Se μ≠0, os dois jets cruzados de dslope χ são iguais a χ₂, mas não conjugados.
`phase_obstructs_isolated_hermitian` formaliza a falha da condição hermitiana nesses
dois jets do kernel isolado sob a hipótese explícita μ≠0. Logo esse canal isolado
não poderia ser anunciado como Gram de Hilbert nessa situação.

**Não se anuncia um NO-GO nativo incondicional:** μ≠0 ainda precisa de um
certificado da fonte infinita. A obstrução também não se aplica ao ledger
completo, que conserva precisamente as compensações demonstradas acima.

`experiment.py` usa `Fraction` nas duas componentes complexas. Ele verifica
16 pares de nós, incluindo a diagonal com derivadas verdadeiras, três
resíduos de fase não nulos e quatro famílias retangulares centralizadas.
São controles SINTÉTICOS, não uma certificação da fonte canônica.

`native_canary.py` é separado. Monta primeiro os vetores completos de
prefixo (seed, todas as diferenças materiais e retorno de células C2),
para log(n)^m/√n, m=0,1,2, e só depois calcula os pareamentos. Com 1.000,
5.000, 20.000 e 100.000 células, o coeficiente imaginário estimado passa de
−0,2846664705 a −0,2846680061. Não usa theta, momentos canônicos, zeros nem
alturas. Os projetores e forcing desse canário são os de CADA prefixo,
não valores exatos dos objetos infinitos. **Não há cota certificada das
caudas infinitas**, nem esses números são premissas Lean.

## D — O que permanece aberto e validação

Não foram provados μ<0, μ≠0 ou a anulação de toda a fase. O que está no
kernel é a fórmula física do coeficiente, a expansão com resto analítico,
a compensação do numerador e a confluência do agrupamento preservado.

Também não há sinal separado de T̃ ou Dcomp, contratividade geral do retorno,
nova representação Gram completa ou positividade canônica em toda ordem.
O transporte da #41 é preservado sem antecipar o sinal do novo pivô.

Os quatro módulos novos têm 42 teoremas públicos e dez definições,
auditados em 52 raízes, mais o helper privado percorrido transitivamente.
`Audit.lean` usa `#print axioms` e um guard de TIPOS E CORPOS. Os únicos
axiomas permitidos são `propext`, `Classical.choice`, `Quot.sound`.
Rejeitam-se os certificados H6/K6/H7 e a positividade geral do retorno.
Os grupos orbit e phase também rejeitam `material_scale_pos`: o novo
coeficiente de fase e sua regularidade não recebem aquele sinal como
entrada. A analiticidade do residual canônico usa legitimamente a escala
central não nula já demonstrada; não usa sinais posteriores.

`validate.py` executa 16 verificações: inventário, cinco compilações com
warnings como erros, controles racionais, execução numérica separada,
build focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/
Analysis, regressão das doze fontes, histórico inalterado e diff check.
**As 16 verificações passaram.** Os fechamentos transitivos têm 5.326
constantes no grupo orbit, 5.358 no phase, 5.408 no ledger e 5.525 no
confluence. O sucesso da execução numérica significa que o canário rodou, não que
seu sinal infinito foi certificado. Logs, hashes, refs e proveniência ficam
em `evidence/`.

Reprodução no ambiente canônico preparado pela #55:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/native-green-phase-compensation/validate.py
```

As dependências de pesquisa #37/#41/#53/#54/#55 são explícitas no script
de compilação, sem presumir sua incorporação à main. Fonte, amplitudes,
fases, duas pernas, cruzamentos, métrica, domínios, retorno, completion,
normalizações e pins foram conservados. Nenhuma worktree foi criada ou
removida; os arquivos alheios não rastreados foram preservados.

## E — Próximo passo mínimo

A obrigação de confluência do GRUPO COMPENSADO está agora demonstrada.
Não é necessário assumir χ real ou apagar a segunda quadratura.

O teste mais curto ainda aberto para fechar o diagnóstico da fase é
certificar o sinal de

\[
\mu=2\operatorname{Re}\langle w,QJ_2\rangle+
 2\|w\|^2\operatorname{Re}\kappa
\]

com erros provados para as caudas dos vetores materiais e dos retornos de
células. Os canários sugerem que uma caixa racional grosseira, por exemplo
−3/10<μ<−1/4, bastaria; isso é uma META DE CERTIFICAÇÃO, não uma hipótese
usada nos teoremas. Não é preciso calcular milhares de momentos nem
alterar qualquer normalização.

Para o sinal canônico, o próximo objeto correto é a soma T̃+Dcomp,
avaliada no residual exato da #41, com uma estimativa relativa independente
do novo pivô. A compensação agora tem expressão física e valores
confluentes legítimos. Sua positividade continua sendo uma obrigação
adicional, não uma consequência automática da regularidade obtida.
