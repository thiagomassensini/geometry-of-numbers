# Origem vetorial Green do primeiro termo entre regularizações

**Classificação: PARTIAL para positividade canônica all-order.**
A obrigação local é localizar, nos vetores Green originais e em seus nove
cruzamentos, o termo crescente encontrado pela PR #110. A recomposição
abaixo é independente do teorema escalar assintótico daquela PR.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-cross-radial-green-leading`.
Base exata: `996c9baaab86292d9994d009f5ce3364ca1087c5`, head da PR #110,
aberta, draft e sem merge no reconhecimento. A entrega é empilhada sobre
`agent/native-cross-radial-complete-pairing`; main permanece intacta.

## A — O que já estava demonstrado

`completed_source_three_parts` e `weighted_physical_reconstruction`
reconstroem a fonte inteira usando os operadores físicos Green, o retorno
com DOIS traços e o commutator exato de completion. A PR #110 estendeu o
pareamento a dois índices radiais independentes e conservou os nove
cruzamentos. Seu teste J0(k),J1(2k+1) identificou

\[
\delta_k G(J_{0,k},J_{1,2k+1})\to A=i\sqrt2 h_0/6,
\qquad\delta_k=1/(k+1).
\]

As identidades nativas `incident_amplitude_response`,
`radial_weight_difference` e `response_radial_readout` já descrevem os
pesos das duas pernas pela mesma característica completada. Reutilizamos
as expansões da resposta e o resto `nativeRemainder 2`, as calibrações dos
jets radiais e a Gram Cauchy física original. Não se reabre a construção
dos momentos, a ortogonalização da PR #41 ou os certificados finitos.

## B — O que foi demonstrado agora

### 1. As três partes como vetores físicos, antes do pairing

`partField` apenas nomeia os operadores que JÁ ocorrem em
`completedSourceParts`. Para um input finito c e um peso w, escrevemos
V_a(w,c), a=0,1,2, respectivamente:

\[
\begin{aligned}
V_0(w,c)&=G_\eta S(w B_\eta c),\\
V_1(w,c)&=R_\eta^2\bigl[w_0c_0\phi_0+
 (w_1c_1-2\eta w_0c_0)\phi_1\bigr],\\
V_2(w,c)&=G_\eta S([B_\eta,w]c).
\end{aligned}
\]

S é a síntese Cauchy existente, B_η é `finiteTfvdBulk`, e G_η,R_η são os
operadores Green/resolvente físicos existentes. O domínio é 0<η<1 e
inputs finitos. Não se introduz operador, fonte ou métrica ajustada.

`completed_part_as_fields` prova a igualdade com as DUAS pernas do estado
original. `part_field_reconstruction` prova Σ_a V_a(w,c)=S(wc).
`part_field_finite_locality` conserva o suporte de c, o suporte REAL de
B_ηc e ambos os endereços de bordo, incluindo o halo necessário.

Definimos C_a(c)=V_a(1,c), W_a(c)=V_a(p1,c), com p1(j)=j+1.
Esses vetores são construídos ANTES de usar os momentos como coeficientes.

`native_part_coordinates` e `native_part_contrast_mean` transportam as
coordenadas completas de cada parte. Se P_{k,a}(c) é a parte física nativa,
κ=k+1, D=2i/√2, Q_{k,a}(c)=V_a(q_k,c), então

\[
\boxed{
 P_{k,a}^{+}-P_{k,a}^{-}=\sqrt\kappa D C_a(c),\qquad
 \frac{P_{k,a}^{+}+P_{k,a}^{-}}2=\sqrt\kappa D Q_{k,a}(c).
}
\]

As duas coordenadas recuperam integralmente as duas pernas. Não se afirma
que essa mudança de coordenadas seja uma isometria positiva da forma
assinada. A regularidade é descarregada em um prefixo finito derivado dos
suportes reais; não depende de sinais dos momentos.

### 2. Expansão VETORIAL da mesma resposta e do mesmo resto

`part_response_expansion` prova, para qualquer c finito e para as três
partes simultaneamente, eventualmente perto de z=0:

\[
V_a(q_z,c)=h_0z W_a(c)-h_1z^3 V_a(p3,c)
             +z^5 V_a(\mathcal R_2(z),c).
\]

Aqui p3(j)=(j+1)^3 é um peso de ENDEREÇO, não o jet J3 ou uma profundidade
vertical. `remainderSamples 2 z` retém o MESMO `nativeRemainder 2` em cada
endereço. `part_remainder_continuous` controla esse resto como VETOR físico,
inclusive no commutator. Não é uma estimativa posterior de energias separadas.

`normalized_part_expansion` mantém o erro exato; `normalized_part_tendsto`
prova κ V_a(q_k,c)→h0 W_a(c). A multiplicação por κ é uma observação
analítica, cuja igualdade com a fonte original é provada; não muda suas
amplitudes ou sua métrica.

### 3. A compensação pode ser vista antes de escalarizar

`even_vector_compensation` prova, para E=nativeEvenProfile 0,

\[
\boxed{
(C_0(E),C_1(E),C_2(E))=(u,v,0),\qquad
(W_0(E),W_1(E),W_2(E))=(2u,v,-u).
}
\]

Não se escolhem u,v para produzir essa igualdade: são os campos físicos
constantes, e a prova calcula o bulk e o commutator originais. Em particular,
`linear_even_residual` identifica

\[
W_2(E)=-\eta G_\eta\phi_1.
\]

`linear_even_residual_ne_zero` prova W2(E)≠0 a partir de
`green_seed_cross_re_pos`, que é um pareamento positivo do operador Green
físico. Essa prova NÃO usa h0>0, nenhum sinal de Hankel ou certificado theta.
O componente extra do bulk é compensado pelo vetor de completion, antes
do pairing. A soma continua u+v=φ0 pela reconstrução original.

### 4. Os nove coeficientes do cruzamento original

`native_parts_pair` extrai o pareamento SOMENTE depois das identidades
vetoriais, com as duas regularizações e as duas respostas conservadas.
`partCross` é literalmente o pairing dos componentes físicos de J0(k)
e J1(2k+1); a calibração do jet ímpar conserva seu fator e sua fase.

`part_cross_scaled_identity` mantém as duas observações vetoriais
normalizadas explícitas. `part_cross_scaled_tendsto` prova, para todos
os nove pares a,b,

\[
\boxed{
\delta_k G_{ab}(k)\to L_{ab},\qquad
L_{ab}=\sqrt2 h_0\left[
 \langle C_a(E),W_b(O)\rangle+
 2\langle W_a(E),C_b(O)\rangle\right],
}
\]

onde O=nativeOddProfile 0 é o input ORIGINAL i(e0−e1). A forma usada é a
forma complexa assinada original. Não se presume positividade ou simetria
do kernel ponderado, nem se elimina qualquer quadratura.

Os lemas `leading_residual_row`, `leading_residual_column` e
`leading_residual_residual_zero` registram exatamente a estrutura:

| Componente | Coeficiente retido |
| --- | --- |
| Linha residual, b=0,1 | 2√2 h0 ⟨W2(E), C_b(O)⟩ |
| Coluna residual, a=0,1 | √2 h0 ⟨C_a(E), W2(O)⟩ |
| Residual–residual | 0, por C2=0 provado vetorialmente |
| Bulk/bordo, a,b=0,1 | Os dois pareamentos ordenados da fórmula L_ab |

O vetor W2(E) não nulo NÃO prova que todos esses cruzamentos sejam não
nulos, nem que sua soma tenha um sinal determinado. Eles permanecem
explícitos para que qualquer cancelamento seja demonstrado.

### 5. Recomposição independente pela Gram original

`sum_leading_eq` usa a reconstrução vetorial das quatro somas e APENAS
então calcula seus pareamentos pela Gram Cauchy ⟨φ_i,φ_j⟩=1/(i+j+2):

\[
\sum C(E)=\sum W(E)=\phi_0,\quad
\sum C(O)=i\phi_0-i\phi_1,\quad
\sum W(O)=i\phi_0-2i\phi_1.
\]

As duas ordens somadas dão −i/6 e i/6; portanto

\[
\boxed{\sum_{a,b}L_{ab}=\sqrt2h_0(-i/6+2i/6)=i\sqrt2h_0/6=A.}
\]

`part_cross_sum` mantém a igualdade exata com a fonte completa em todo k.
`recomposed_leading_tendsto` recupera o limite da PR #110 a partir dos
NOVE limites físicos recém-provados. A auditoria proíbe usar os teoremas
escalares `doubled_scaled_tendsto`, `doubled_scaled_expansion`,
`doubled_unscaled_expansion` e `doubled_next_tendsto` como atalhos.

## C — O que foi refutado ou separado

O contraste constante nulo e o termo residual–residual nulo não autorizam
apagar a correção. Seu perfil linear W2(E) é um vetor Green não nulo,
independentemente do sinal de qualquer momento. A compensação (2u,v,−u)
mostra concretamente qual informação se perderia ao fazer isso.

Não se refutou uma síntese global nem se identificou uma direção negativa
da Hankel. Tampouco se provou que cada cruzamento residual seja não nulo
ou que não haja cancelamento de sua soma. A positividade do pareamento
Green que certifica um vetor não nulo não é positividade da forma assinada
canônica.

## D — O que permanece aberto

O termo crescente foi localizado nas coordenadas vetoriais físicas, com
os nove coeficientes e sua soma demonstrados. Não se construiu uma
isometria que identifique regularizações, nem se removeu o defeito por
uma alteração da fonte. A forma real dos momentos em toda ordem continua
sem uma lei independente que determine seu sinal.

A expansão vetorial é válida para TODO input finito. O resultado de
coeficientes L_ab é o teste J0(k),J1(2k+1); não se anuncia controle
uniforme na ordem dos jets ou um operador infinito positivo.

η é o parâmetro Green existente, k é regularização radial; nenhum deles
é identificado aqui com profundidade vertical, câmera ou deformação
centro–pernas. Fontes, amplitudes, fases, duas pernas, bordos, completion,
retorno, Gamma, métricas, pins e trabalhos antigos foram preservados.

## E — Próximo passo mínimo

A expansão vetorial já retém o termo cúbico. O teste curto seguinte é
confrontar o coeficiente B da PR #110 NOS MESMOS nove cruzamentos, sem
usá-lo como premissa. A candidata concreta é

\[
\kappa\bigl(G_{ab}(k)-\kappa L_{ab}\bigr)\to
-\sqrt2h_1\left[\tfrac14\langle C_a(E),V_b(p3,O)\rangle+
2\langle V_a(p3,E),C_b(O)\rangle\right].
\]

Seu somatório deve reproduzir 5i√2 h1/24 pela reconstrução vetorial. Essa
lei por componente NÃO foi formalizada nesta rodada. É uma regressão
curta do mesmo transporte, não uma hipótese nova de positividade.

Para avançar no sinal all-order, a obrigação segue sendo uma desigualdade
relativa da fonte COMPLETA, controlando bulk, ambos os bordos e seus
cruzamentos com o complemento. Mais coeficientes assintóticos, por si
sós, não fornecem essa lei. Não rebatizar o próprio sinal desejado como
uma causa geométrica já demonstrada.

### Reprodução e validação

No host canônico llm, em checkout desta branch com o cache canônico:

```bash
cd research/native-cross-radial-green-leading
python3 validate.py
```

O modo normal recompila os 53 ancestrais intactos da base. A opção
`--reuse-upstream` exige os hashes registrados das fontes E `.olean`.
Os quatro módulos novos e Audit são sempre compilados explicitamente
com `lean -DwarningAsError=true`, além dos builds `lake build --wfail`,
auditorias Foundation/Geometry/Analysis e conferência de preservação.

**Os 15 checks locais passaram com código de saída zero.** São 31
teoremas, quatro definições e duas abreviações novas: 37 raízes públicas,
todas com `#print axioms` e auditoria transitiva dos tipos E corpos.

| Grupo | Raízes | Dependências únicas | Controles |
| --- | ---: | ---: | --- |
| Construção vetorial | 26 | 5.519 | Momentos canônicos proibidos |
| Extração e recomposição | 11 | 5.733 | Mesma fonte, sem certificados de sinais |

Ambos os grupos bloqueiam os certificados preexistentes de sinal h0/h1,
os consumidores posteriores de positividade finita e os quatro teoremas
escalares assintóticos da PR #110 listados em B.5. Assim a recomposição
não recebe como premissa o coeficiente escalar que deveria explicar.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos na
análise; Foundation mantém sua auditoria própria. Não há `sorry`, `admit`,
`native_decide` ou axiomas matemáticos novos. Não se reivindica footprint
vazio para a camada analítica.

`evidence/validation.json` registra comandos, logs e saídas;
`evidence/lean-Audit.log` contém os certificados e `public-roots.json`
lista todas as raízes. `evidence/upstream.json` registra os hashes das
fontes e `.olean` dos 53 ancestrais recompilados. O bootstrap e seu
registro documentam essa compilação. `source-provenance.json`,
`preservation.json` e `SHA256SUMS` registram fontes, pins, arquivos antigos
protegidos e integridade. Quando necessário, espaços finais dos logs
foram normalizados conservando o bruto em `.raw.log.gz` com hash.
Os resultados são locais; não se afirma sucesso de CI remoto.

A publicação é draft sobre a PR #110, sem merge em main. O commit e a URL
são registrados na entrega externa. A cópia local completa e seus hashes
são verificados antes de remover apenas a worktree desta rodada.

**Fim do relatório — PARTIAL para positividade all-order; origem vetorial
Green, nove coeficientes e compensação da fonte demonstrados sem apagar o complemento.**
