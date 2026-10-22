# TFVD completo e sinal do residual Green canônico

**PARTIAL.** O TFVD original fornece uma leitura sem perda do estado material
completo e transporta exatamente o Green compensado e o residual canônico.
A investigação não encontrou uma nova desigualdade positiva para todos os
pivôs. Demonstrou duas obstruções específicas a atalhos de positividade:
a separação causal Green/retorno é oblíqua, e o negativo da segunda diferença
ponderada não é uma forma positiva, mesmo em estados com os dois dados de
bordo nulos, na amplitude crítica binária original.

Base imutável: `6be076db618ee660aec81b73c00e7b754cc72eef` (PR #56).
Branch: `agent/tfvd-complete-green-residual`.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
PR independente, empilhada sobre a #56, sem merge automático.
Main local e remota na abertura: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
O operador foi consultado sem modificações. Worktrees antigas e arquivos
alheios não rastreados foram preservados; nenhuma worktree foi criada.

## A — O que já estava demonstrado

O TFVD vertical já estava fechado por `realCarryTfvdSynthesis_comp_analysis`
e `realCriticalCarryTfvd_identity` em `RealCarryTfvd.lean`:

\[
G_\eta B_\eta+R_\eta\operatorname{Tr}_\eta=I,
\qquad \eta_b=b^{-1/2}.
\]

O estado contém curvatura discreta e DOIS dados de bordo. O parâmetro vertical
não é raio horizontal, índice material nem parâmetro espectral.

`BaseTwoPhysicalEdgeTfvdBridge.lean` já fornecia
`baseTwoPhysicalResidualTfvdAnalysis_injective`: a análise conserva todas as
fibras core/direção/quadratura e as arestas materiais residuais. Estas últimas
não são descartadas. `CarryMaterialTfvdGreenReadout.lean` já fornecia
`carryMaterialTfvd_edge_pairing`, com os quatro cruzamentos GG, GR, RG, RR,
e a compatibilidade da análise com a derivada material. Essa compatibilidade
não identifica os dois eixos: TFVD e derivada material podem ser usados juntos.

A PR #41 construiu a funcional e os polinômios mônicos residuais sem assumir
positividade. `exact_even_green_residual` usa apenas os pivôs anteriores não
nulos para identificar o residual par com o pivô; `exact_odd_green_residual`
identifica o setor deslocado. Os nomes efetivos e hipóteses estão em
`research/forcing-centered-native-residual/CriticalGreen.lean`:

\[
J_0(p,q)=\mathcal L(pq)-\mathcal L(p)\mathcal L(q)/h_0,
\qquad J_1(p,q)=\mathcal L_1(pq).
\]

No polinômio exato P da #41, o valor correspondente é o pivô assinado.
Isso não transforma uma família vertical arbitrária em fonte canônica.

A #56 fornecia `compensated_source_factor`,
`compensated_diagonal_confluence` e `canonical_confluent_pullback`, conservando
a fase e o grupo central/comprimido/oculto. A derivada positiva obtida na #55
é o resultado LOCAL χ′(0)=2‖w‖²>0; não é positividade canônica all-order.

## B — O que foi demonstrado agora

### 1. Coordenadas compatíveis do MESMO estado completo

`CompleteTfvd.lean` define `materialAnalysis` sobre o carrier original:

\[
Y=(\mathrm{seed},\mathrm{gradiente},\mathrm{retorno\ global})
\longmapsto
(\mathrm{seed},\mathrm{TFVD\ físico},\mathrm{arestas\ residuais},
 \mathrm{retorno\ global}).
\]

`materialAnalysis_injective` usa a injetividade já provada da análise física
com residual. `materialCoordinates` é a equivalência linear com a IMAGEM
compatível dessa análise; `material_roundtrip` e `material_data_roundtrip`
provam os dois roundtrips. Não se declara que qualquer tupla de canais é
física. Nenhuma métrica é introduzida nessa imagem, nem se afirma isometria,
whitening ou continuidade de uma inversa para uma nova norma de canais.

`source_data` identifica os dados da fonte original. O retorno global de
células completas continua presente e é distinto do retorno de traço dentro
de cada fibra TFVD. `green_roundtrip` transporta o Green original com dois
argumentos independentes, DEPOIS da reconstrução completa. Readout e redução
originais também são preservados. Isso fecha uma interface tipada; não é
uma nova lei de sinal.

### 2. Transporte do ledger físico completo ao residual canônico

`GreenTransport.lean` constrói `tfvdCompensatedGreen`, `tfvdMixedGreen` e
`tfvdWholeGreen` avaliando os pares originais nas coordenadas compatíveis.
Mantém central, comprimido, ambos os cruzamentos com forcing, forcing/forcing,
complemento oculto e a MESMA compensação de fase. Não muda dressing, fonte,
normalizações, domínio do clock ou momentos.

- `tfvd_compensated_exact` e `tfvd_mixed_exact` são igualdades de funções
  nos dois parâmetros independentes.
- `tfvd_compensated_confluence` preserva o verdadeiro limite furado em CADA
  ponto da diagonal numa vizinhança da origem, herdado da #56.
- `tfvd_whole_factor` demonstra, numa vizinhança aberta da fonte,

\[
\mathscr G^{\rm TFVD}_{\rm completo}(t,u)=(u-t)\,\mathcal B(t,u),
\]

onde \(\mathcal B\) é `completedCoefficient` ORIGINAL da #37.

- `tfvd_native_residual_regular` demonstra, com t,u não nulos, distintos e
  resposta F não nula em ambos,

\[
\frac{\mathscr G^{\rm TFVD}_{\rm completo}(t,u)}
 {(u-t)\,2h_0^2tu\,\overline{F(t)}F(u)}
 =\mathfrak R(t,u).
\]

Aqui \(\mathfrak R\) é `carryMaterialRealResidual`, cuja extração polarizada
já alcança os mesmos J₀/J₁ e polinômios da #41. Dividem-se somente fatores
literais da identidade original na carta regular; a fonte não é normalizada
de novo. Não se atribui uma convenção 0/0 ao residual na origem. Os resultados
confluentes anteriores continuam necessários para a extração de jets.

### 3. Reconstrução causal complementar, porém oblíqua

Em `ObliqueTfvd.lean`, sejam
\(P_\eta=G_\eta B_\eta\), \(Q_\eta=R_\eta\operatorname{Tr}_\eta\).
Foram demonstradas as identidades

\[
P+Q=I,\qquad P^2=P,\quad Q^2=Q,\quad PQ=QP=0.
\]

Isso é complementaridade ALGÉBRICA. `vertical_pairing` e `vertical_energy`
conservam os cruzamentos na métrica vertical original:

\[
\|x\|^2=\|Px\|^2+\|Qx\|^2+2\langle Px,Qx\rangle.
\]

`vertical_mixed_witness` fornece a testemunha exata de suporte finito e₂,e₀:

\[
\langle P_\eta e_2,Q_\eta e_0\rangle=-\eta^2.
\]

Portanto `vertical_not_orthogonal` exclui ortogonalidade dos dois subespaços.
Na amplitude binária nativa, `critical_two_mixed_witness` dá EXATAMENTE −1/2.
Os e_j são coordenadas do Hilbert vertical já existente, não momentos novos.

### 4. A identidade discreta de energia contém um termo negativo

Em `DiscreteSign.lean`, U é o shift unilateral vertical original. Não é
síntese TFVD nem evolução no tempo material. O stencil sem a correção de
cabeça é

\[
B^{\rm core}_\eta=\eta^{-1}U^*-2I+\eta U.
\]

`weighted_core_energy` demonstra, para TODO x do ℓ² real original,

\[
\boxed{
-\langle x,B^{\rm core}_\eta x\rangle
=\frac{\eta+\eta^{-1}}2\|Ux-x\|^2
 -(\eta+\eta^{-1}-2)\|x\|^2.}
\]

`weighted_centered_energy` mantém explicitamente o termo de cabeça da
segunda diferença realmente usada pelo TFVD:

\[
-\langle x,B_\eta x\rangle
=\frac{\eta+\eta^{-1}}2\|Ux-x\|^2
 -(\eta+\eta^{-1}-2)\|x\|^2
 +x_0(\eta^{-1}x_1-2x_0).
\]

`weighted_negative_bulk` prova, para 0<η<1,

\[
\eta+\eta^{-1}-2=(1-\eta)^2/\eta>0.
\]

Logo há uma contribuição de massa NEGATIVA. Não se pode substituí-la por
zero, usar o Laplaciano não ponderado ou alterar a métrica por um gauge.
Esta é uma identidade da forma vertical de curvatura; NÃO se afirma que
essa forma, isoladamente, seja o Green canônico completo.

## C — O que foi refutado

1. **TFVD causal como separação ortogonal automática:** refutado pelo
   cruzamento exato −1/2. A reconstrução sem perda continua válida.

2. **Negativo do bracket ponderado como soma positiva universal em dados
   de traço zero:** refutado na amplitude crítica original. Definimos somente
   a testemunha de suporte finito

\[
x=\sum_{k=0}^{17}e_{k+2}.
\]

`plateau_trace_zero` prova OS DOIS dados de bordo nulos.
`plateau_curvature_energy` calcula exatamente

\[
\langle x,B_\eta x\rangle=17(\eta+\eta^{-1})-36.
\]

Para η=2⁻¹/², η⁻¹=2η e
\(\eta>12/17\), porque \(1/2-(12/17)^2=1/578>0\).
`critical_plateau_negative_laplacian` e
`critical_no_tracezero_laplacian_positive` concluem

\[
-\langle x,B_{\eta_2}x\rangle=36-51\eta_2<0.
\]

Isso é um NO-GO para a desigualdade vertical universal acima. **Não é uma
direção negativa da Hankel canônica:** não se demonstrou que essa testemunha
seja um residual canônico da fonte completada. Não se refuta a geometria,
a reconstrução TFVD, nem outra realização física com seus termos completos.

3. Não foi provado que a fase nativa seja não nula, que o grupo compensado
   tenha sinal negativo ou que algum pivô canônico novo seja negativo.

## D — O que permanece aberto e validação

A equivalência de coordenadas conserva o mesmo kernel; não cria uma razão
para ele ser positivo. Não há nova representação Gram positiva completa,
nova margem no residual da #41, contratividade all-order ou construção de
alturas sem as hipóteses espectrais legítimas.

O código da coordenada usa `LinearEquiv.ofInjective` sobre a IMAGEM da análise,
sem pedir PosDef. O Green sobre os dados é definido pela decodificação e pela
FORMA ORIGINAL. Portanto seu transporte exato não deve ser apresentado como
uma descoberta de positividade. O avanço de sinal desta rodada é a localização
formal dos termos que impedem dois atalhos, com testemunhas exatas.

Os quatro módulos matemáticos são compilados explicitamente por
`compile_module.sh`, com warnings como erros. `Audit.lean` imprime axiomas de
TODAS as raízes públicas e percorre tipos/corpos transitivamente. Só são
permitidos `propext`, `Classical.choice`, `Quot.sound`; os consumidores de
positividade H6/K6/H7 e a positividade geral do retorno são rejeitados.
As identidades verticais e de coordenadas também rejeitam `material_scale_pos`.
O uso de h₀≠0 na carta regular canônica é o resultado central anterior, não
uma hipótese de sinal do pivô novo.

`experiment.py` contém controles racionais exatos FINITOS do stencil, dos
cruzamentos e da desigualdade racional da amplitude. Não é certificado dos
momentos, não testa zeros, alturas ou theta, e não substitui as provas Lean.
A truncagem da sequência geométrica usada num controle de cruzamento é lida
só contra e₂; não se anuncia uma igualdade de energias de caudas truncadas.

`validate.py` executa os cinco módulos (incluindo Audit), builds focado/raiz
com `lake build --wfail`, auditorias Foundation/Geometry/Analysis, regressão
das doze fontes, controles racionais, comparação de arquivos históricos e
verificação do diff. Logs, hashes e resultados ficam em `evidence/`.
O resultado efetivo da execução é registrado em `evidence/checks.json`.
**As 15 verificações passaram**, incluindo a regressão das doze fontes.
São 32 teoremas e 13 definições/abreviações, em 45 raízes públicas auditadas.
Os fechamentos transitivos de tipos/corpos têm 5.884 constantes no grupo
coordinates, 3.794 no oblique, 3.754 no discrete e 5.963 no ledger.
Só os três axiomas fundacionais permitidos foram encontrados. A ausência
de sinais finitos posteriores como dependências foi verificada pelo guard.

Reprodução no ambiente canônico preparado pela #56:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/tfvd-complete-green-residual/validate.py
```

Não há `sorry`, `admit`, novos axiomas matemáticos nem `native_decide`.
Arquivos históricos, amplitudes, fases, câmeras, fonte, métricas, pins,
bordos, retornos e termos cruzados foram conservados.

## E — Próximo passo mínimo

O TFVD é adequado à reconstrução geométrica. A operação, sozinha, não é uma
lei de positividade. O próximo teste deve explorar uma propriedade da FAMÍLIA
NATIVA completada que não vale para um estado vertical arbitrário.

Concretamente: desenvolver uma identidade de somação por partes do
**Green misto completo**, aplicada aos pares que efetivamente geram os
polinômios residuais Pₛ,ₙ da #41, conservando todos os termos centrais,
comprimidos, forcing e ocultos. A identidade vertical acima serve de teste:
se nela aparecer o stencil original, seu termo negativo de massa e seu
termo de cabeça têm de reaparecer com os coeficientes corretos. Não foi
provado que o Green completo se reduza a essa forma vertical.

A obrigação de sinal só será reduzida se uma relação independente da fonte
controlar os termos assinados nessa família, com margem sobrevivente; receber
Jₛ(P,P)>0 ou a contratividade equivalente como hipótese não resolve a questão.
Não é necessário reabrir a reconstrução TFVD, modificar a fonte, calcular
milhares de momentos ou presumir que os coeficientes da #41 sejam um clock
Krylov material (rota já excluída pela #36).

**Resposta à proposta:** o TFVD encaixa exatamente na proveniência e
preserva o residual procurado. Ainda não fornece a lei de sinal. A rodada
formalizou o transporte completo e refutou duas inferências automáticas,
com alcance delimitado. Resultado PARTIAL; a ponte positiva da fonte
completada permanece aberta.
