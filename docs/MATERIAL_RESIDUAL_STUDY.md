# Carry — o residual da redução da fonte material

Data: 2026-10-16. Repositório alterado: `geometry-of-numbers`, base `87597b95c398d6d70c5db5793cecd646a45ae7dd` (PR #5). Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` (PR #106).

**Resultado:** o residual do primeiro canal foi definido diretamente a partir da resposta material existente e identificado localmente com a redução já construída da fonte canônica. A identidade foi estendida à diagonal real pelas derivadas corretas. Ela agora fornece uma decomposição da energia para qualquer família finita de parâmetros reais próximos de zero, incluindo repetições, sem perder cruzamentos.

**O residual não desaparece.** Ele zera na linha central, mas sua diagonal é estritamente positiva em todo parâmetro real não nulo suficientemente próximo de zero. Isso é positividade pontual da diagonal, não positividade de todas as matrizes finitas. A identificação com um Gram físico completo continua aberta.

## 1. Qual residual está sendo estudado?

O PR #5 construiu a companheira no domínio do relógio material existente. O estado completo, seu readout e seu dressing permanecem:

\[
Y_t=(1,g_t,\beta_t),\quad S_t=\ell(Y_t),\quad
F(t)=D(t)S_t,\quad
\mathcal C_t(y)=-[D(t)(-iKy)+D'(t)y].
\]

A identificação provada do par de readouts é

\[
(\ell(\mathcal C_t(Y_t)),\ell(D(t)Y_t))=(-F'(t),F(t)).
\]

Assim, a resposta material é a definição anterior

\[
r_0(t)=\frac{\ell(\mathcal C_t(Y_t))}{2\ell(D(t)Y_t)}.
\]

No domínio usual F≠0, essa expressão é −F′/(2F). Nenhuma constante foi ajustada; a contribuição D′ e o retorno global do relógio já estão no readout. A bruta sequência material não foi colocada em ℓ²; foi usado o carrier completado de semente, gradiente e retorno.

Definimos apenas uma nova função, `carryMaterialReducedResponse`, sobre o parâmetro real:

\[
a(t)=\operatorname{dslope}r_0(0,t),\quad
\alpha=\operatorname{Re}a(0),\quad \phi(t)=a(t)/\sqrt\alpha,
\qquad
\boxed{r_1(t)=\frac{\operatorname{dslope}a(0,t)}{\alpha a(t)}.}
\]

As definições de a, α e φ já eram do PR #5. `dslope f(t,t)` significa `deriv f t`. Para t≠u é (f(u)−f(t))/(u−t). A redução não recebe uma matriz de momentos, um kernel positivo ou uma norma como entrada.

Os quocientes de Lean são totais. Sua interpretação como quocientes usuais e a identidade local abaixo usam a regularidade e a não anulação já fornecidas pelo germen da fonte. Nenhuma afirmação global é feita nos zeros de denominadores.

## 2. Identificação com a mesma fonte canônica

No verificador [CanonicalComparison.lean](../research/material-central-calibration/CanonicalComparison.lean), o namespace `CarryMaterialResidualComparison` prova:

- `material_reduced_eventually_eq`: r1 material é a restrição real do `SourcePositiveReduction.reducedResponse` existente, numa vizinhança de zero.
- `material_reduced_zero`: r1(0)=0.
- `material_reduced_hasDerivAt_zero` e `material_reduced_deriv_real_pos`:

\[
\boxed{r_1'(0)=h_1/h_0^2>0.}
\]

- `material_reduced_not_zero_germ`: r1 não é identicamente zero em nenhuma vizinhança de zero.
- `material_response_conj`, `material_axis_conj`, `material_reduced_conj`: as três respostas preservam a realidade sobre o eixo real, expressa pela conjugação.
- `material_reduced_deriv_continuous`: a derivada real de r1 é contínua na origem.

Reutilizam-se o germen analítico escalar, a positividade já certificada de h0 e h1 e a igualdade do readout material com a característica. Não se postula holomorfia do estado vetorial Y. A restrição complexa→real é justificada para as funções escalares efetivamente identificadas.

## 3. A diagonal real foi fechada

O PR #5 só dividia a identidade do numerador quando os parâmetros reais eram distintos. O quociente complexo bruto `reducedKernel` não fornece sozinho a extensão na colisão: a divisão total 0/0 ali não é a derivada.

`material_real_kernel_split` prova que existe um aberto real U, 0∈U, tal que, para **todos** t,u∈U,

\[
\boxed{
\operatorname{dslope}r_0(t,u)
=\langle\phi(t),\phi(u)\rangle
+\overline{r_0(t)}r_0(u)\operatorname{dslope}r_1(t,u).
}
\]

Usa-se o produto interno complexo padrão, conjugado no primeiro argumento. Ele é a notação já adotada para as duas quadraturas reais; nenhuma métrica foi substituída. Em t=u, a igualdade lê-se

\[
\boxed{r_0'(t)=|\phi(t)|^2+|r_0(t)|^2r_1'(t).}
\]

A prova transporta a igualdade existente fora da diagonal e usa continuidade das duas inclinações divididas e do canal para passar ao limite numa vizinhança perfurada. Não se divide por zero nem se define a diagonal por conveniência.

## 4. Energia finita com todos os cruzamentos

`material_real_finite_energy_split` usa o mesmo U, **independente de N**. Para N arbitrário, tᵢ∈U e cᵢ complexos arbitrários:

\[
\boxed{\begin{aligned}
\sum_{i,j}\bar c_i c_j\operatorname{dslope}r_0(t_i,t_j)
={}&\left|\sum_i c_i\phi(t_i)\right|^2\\
&+\sum_{i,j}\overline{c_i r_0(t_i)}\,c_jr_0(t_j)
\operatorname{dslope}r_1(t_i,t_j).
\end{aligned}}
\]

Estão presentes i=j, i≠j e parâmetros repetidos. Os coeficientes complexos preservam ambas as quadraturas; coeficientes reais são uma especialização. A expressão é uma identidade, sem hipótese de sinal para a segunda soma.

`material_real_energy_on_positive_nullspace` especializa o resultado a

\[
\sum_i c_i\phi(t_i)=0.
\]

Nessas famílias, a energia completa é **exatamente** a segunda soma. Esse é um teste concreto que a calibração central não resolve: ao cancelar o canal extraído, todo o sinal restante depende do residual, incluindo os cruzamentos.

## 5. O que seu sinal realmente permite concluir

Denotando, apenas neste relatório,

\[
R(t,u)=\overline{r_0(t)}r_0(u)\operatorname{dslope}r_1(t,u),
\]

`material_weighted_residual_center` prova R(0,u)=0 para todo u real. A linha central fica totalmente no canal φ. Isso explica por que a calibração de h0 não detectava o residual.

Por outro lado, `material_weighted_residual_diagonal_pos` prova

\[
\boxed{\operatorname{Re}R(t,t)>0
\quad\text{para todo }0<|t|<\varepsilon\text{, para algum }\varepsilon>0.}
\]

A prova usa r0(t)=t·a(t), a(0)=h0>0 e a continuidade da derivada de r1, cuja parte real em zero é h1/h0²>0. Portanto, o peso não zera fora do centro suficientemente perto dele. `material_weighted_residual_not_zero_germ` exclui formalmente apagar R numa vizinhança.

**Não decorre daí** que todas as matrizes [dslope r1(tᵢ,tⱼ)] ou [R(tᵢ,tⱼ)] sejam positivas semidefinidas. A afirmação sobre a diagonal controla vetores com um único ponto; a afirmação matricial controla combinações e seus cruzamentos. Esta segunda questão continua aberta.

## 6. O segundo canal e os quatro canais já existentes

O repositório do operador já havia construído `secondPositiveFeature`, a partir do eixo de r1 e de sua escala positiva α1. As novas provas transportam seu canal ponderado pela resposta material:

\[
\psi_1(t)=r_0(t)\,secondPositiveFeature(t:\mathbb C).
\]

`material_second_channel_hasDerivAt_zero` e `material_second_channel_firstJet_energy` provam

\[
\psi_1'(0)=\alpha_0\sqrt{\alpha_1},\qquad
\boxed{|\psi_1'(0)|^2=h_1.}
\]

É o **primeiro jet real desse canal escalar**. Não é uma identificação do jet vetorial físico inteiro com um jet canônico nem uma prova de positividade de todos os jets.

As quatro escalas abaixo já estavam certificadas no operador; não são descobertas desta rodada:

\[
\alpha_0=h_0,\quad \alpha_1=h_1/h_0^2,\quad
\alpha_2=\frac{h_0(h_0h_2-h_1^2)}{h_1^2},\quad
\alpha_3=\frac{h_1(h_1h_3-h_2^2)}{(h_0h_2-h_1^2)^2}.
\]

Sua positividade usa certificados próprios da fonte theta e dos primeiros discriminantes. `chain_four_positive_channels_local` e `nativeKernel_four_positive_channels_local` mantêm o residual seguinte com seu peso. Essas identidades complexas têm seus domínios e exclusões de colisões originais; o novo fechamento de diagonal foi provado aqui para a primeira redução no eixo real. Não se afirma que a versão de quatro canais já tenha sido estendida do mesmo modo.

## 7. Dois residuais distintos: uma obstrução literal

Na geometria material, `baseTwoResidualEdgeProjection` é a projeção nas coordenadas que o recorte físico C2 não observa. Isso é um componente do gradiente ℓ², diferente do residual da redução de uma resposta escalar.

O novo teorema de biblioteca `carryMaterial_physical_residual_origin_norm_pos` usa a própria fonte, sem campos livres. A projeção contém a coordenada material zero:

\[
(Qg_0)(0)=g_0(0)=1/\sqrt2-1\ne0,
\qquad \|Qg_0\|>0.
\]

Consequentemente, `material_weighted_residual_not_physical_edge_energy` prova

\[
\boxed{\operatorname{Re}R(0,0)=0\ne\|Qg_0\|^2.}
\]

Isso refuta somente a identificação literal desses dois objetos. Não refuta um futuro transporte com semente, retorno, bordos, completação ou outras correções justificadas. Tampouco transforma o residual escalar em um componente ortogonal do Hilbert material.

## 8. A primeira ponte que permanece aberta

**Fonte disponível → transformação existente → destino → igualdade necessária → lacuna:**

\[
(Y,K,D,\ell)\ \longrightarrow\ (-F',F)\ \longrightarrow\ r_0,a,\phi,r_1
\ \longrightarrow\ \operatorname{dslope}r_0
=\langle\phi,\phi\rangle+R.
\]

Todas essas setas escalares, no domínio real local especificado, têm proveniência demonstrada. Falta uma construção de estados/readouts do restante da **mesma síntese física** cujo pareamento seja exatamente R(t,u), incluindo sua normalização, bordos e cruzamentos. A projeção Qg não satisfaz essa igualdade literal já em (0,0).

Uma realização física positiva de R seria suficiente para a positividade do kernel completo pela identidade finita. Sua existência não foi provada, e não é condição logicamente necessária para toda possível prova de positividade do kernel completo. A condição mínima necessária que a identidade já expõe é: a forma residual deve ser não negativa nas famílias que anulam o canal φ. Fora desse subespaço, a soma inteira continua sendo a obrigação exata.

O próximo teste natural é transportar a segunda extração com a mesma disciplina de diagonal e comparar os cruzamentos genuínos do residual com a síntese física, sem identificá-lo com Qg. Outra via é demonstrar diretamente o controle da forma residual no núcleo do primeiro canal. Nenhuma dessas obrigações está sendo assumida neste relatório.

## 9. Status e validação

| Objeto/afirmação | Status |
| --- | --- |
| Definição da redução a partir da resposta material efetiva | **PROVADO/definido no Lean** |
| Germen comum material/canônico; r1(0)=0; r1′(0)=h1/h0²>0 | **PROVADO no Lean**, reutilizando a fonte certificada |
| Identidade local real de dois parâmetros, inclusive diagonal | **PROVADO no Lean nesta rodada** |
| Decomposição finita para N arbitrário, com cruzamentos e repetições | **PROVADO no Lean nesta rodada** |
| R zera no centro e tem diagonal positiva local fora dele | **PROVADO no Lean nesta rodada** |
| Primeiro jet do segundo canal material tem energia h1 | **PROVADO no Lean por transporte de resultado existente** |
| Quatro escalas positivas e suas fórmulas | **REUTILIZADO**, já provado no operador |
| R é literalmente o Gram da projeção Qg | **OBSTRUÍDO** na origem, para essa candidata |
| Realização física do kernel R com pareamento preservado | **ABERTO** |
| Positividade semidefinida de todas as matrizes residuais | **ABERTO** |
| Gram do estado material inteiro = kernel canônico | **ABERTO**; o no-go anterior para DY permanece |
| Realização positiva do residual implica positividade local do kernel completo | **CONDICIONAL**, consequência da identidade finita; não prova existência |

Biblioteca nova: [CarryMaterialResidualResponse.lean](../GeometryOfNumbers/Analysis/CarryMaterialResidualResponse.lean), uma definição e um teorema. Comparação externa: dezenove teoremas novos no namespace `CarryMaterialResidualComparison`; os 34 anteriores permanecem e foram rechecados. A lista completa dos **21 novos roots** está em [new-roots.json](../research/material-residual-study/new-roots.json).

Validação no servidor `llm`: build focado `--wfail` (8.788 jobs), completo `--wfail` (8.827 jobs), auditorias Foundation/Geometry/Analysis, regressões 72/TFVD/relógio/domínio/retorno e comparação entre repositórios com warnings tratados como erros. Os novos roots foram auditados transitivamente por tipos e corpos, com `#print axioms`; somente `propext`, `Classical.choice` e `Quot.sound`. A Foundation conserva sua auditoria de footprint vazio; isso não é atribuído à camada Analysis.

Comandos, footprints, proveniência de declarações e commits, hashes e logs estão em [research/material-residual-study](../research/material-residual-study/). O verificador externo reutiliza as versões coincidentes de Lean/Mathlib/GreenFrame; não cria dependência Lake nem altera pins. Os repositórios do operador e de momentos foram apenas consultados; seus arquivos preexistentes foram preservados. Nenhum experimento numérico é usado como prova neste resultado.
