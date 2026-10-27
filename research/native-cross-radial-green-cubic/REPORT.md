# Coeficiente cúbico nos nove cruzamentos Green nativos

**Classificação: PARTIAL para a positividade canônica all-order.**
O alvo local é o teste recomendado pela PR #111: extrair o coeficiente
cúbico de cada cruzamento da MESMA fonte J0(k),J1(2k+1) e recompô-lo
pelos vetores físicos, sem usar o coeficiente escalar como premissa.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-cross-radial-green-cubic`.
Base exata: `6df09aefae04dc1923bad144c9230da7b407d349`, head da PR #111,
aberta, draft e sem merge no reconhecimento. A entrega é empilhada sobre
`agent/native-cross-radial-green-leading`; main e PRs anteriores intactas.

## A — O que já estava demonstrado

A PR #111 identifica os vetores `partField` com as três componentes
ORIGINAIS `completedSourceParts`: bulk Green, DOIS bordos e commutator de
completion. A média e o contraste de cada parte foram transportados como
vetores completos, antes do pareamento complexo assinado.

Para qualquer input finito c, `normalized_part_expansion` já preserva
exatamente os termos linear e cúbico e o resto nativo. Para os jets do
primeiro cruzamento, `part_cross_scaled_identity` conserva os dois
campos vetoriais com suas regularizações distintas; `part_cross_sum`
recompõe todos os nove cruzamentos na fonte completa.

Usamos C_a(c)=V_a(1,c), W_a(c)=V_a(p1,c), E=nativeEvenProfile 0 e
O=nativeOddProfile 0=i(e0−e1), mantendo suas fases. p_d(j)=(j+1)^d
é peso de ENDEREÇO, não ordem de jet nem profundidade Carry. O fator
κ=k+1 é de regularização radial; δ=1/κ.

A PR #111 provou δ G_ab(k)→L_ab e recompôs Σ_ab L_ab=A=i√2 h0/6
pela Gram Cauchy original. Essa identidade vetorial anterior é reutilizada.
Os teoremas escalares assintóticos da PR #110 não entram na nova prova.

## B — O que foi demonstrado agora

### 1. A extração vetorial admite qualquer grau Taylor

`part_field_sum_weight` mantém a soma de pesos como vetores inteiros
nos operadores já existentes. `part_full_taylor_expansion` prova, para
TODO N natural e TODO input finito c, nas três partes simultaneamente,

\[
V_a(q_z,c)=\sum_{j<N}(-1)^jh_jz^{2j+1}V_a(p_{2j+1},c)
 +z^{2N+1}V_a(\mathcal R_N(z),c).
\]

`part_full_remainder_continuous` controla o resto como vetor físico.
É o MESMO `nativeRemainder N`, avaliado em cada endereço retido; os
suportes reais, seu halo e ambos os bordos permanecem na síntese.
Essa é uma lei all-order de EXTRAÇÃO TAYLOR para inputs finitos,
não uma lei de sinal nem um resultado sobre todos os pivôs.

### 2. Uma compensação geométrica em qualquer grau de endereço

`seed_address_compensation` prova para todo d natural, no MESMO input E,

\[
\boxed{
(C_0(E),C_1(E),C_2(E))=(u,v,0),\qquad
(V_0(p_d,E),V_1(p_d,E),V_2(p_d,E))
=(2^du,\ v,\ (1-2^d)u).
}
\]

u e v são os vetores físicos constantes já existentes; não são escolhidos
pelos momentos. A prova calcula o bulk real do input, conserva os dois
traços e usa a reconstrução vetorial original para identificar o complemento.
Nenhum momento canônico entra nessa lei.

No caso cúbico, `seed_cubic_compensation` dá exatamente

\[
\boxed{(u,v,0)\longmapsto(8u,v,-7u).}
\]

`seed_cubic_residual_ne_zero` prova que esse perfil cúbico residual é
não nulo, sem usar h1>0 ou positividade Hankel. O perfil não nulo não
implica que todo cruzamento dele seja não nulo ou tenha sinal fixo.

A lei vale para o GRAU DE ENDEREÇO do mesmo primeiro input par. Não
se deve anunciá-la como uma lei sobre toda ordem de jet ou de Hankel.

### 3. O resto cúbico é identificado como vetor antes do pairing

`cubicPart` é somente a observação diagnóstica do erro vetorial já
identificado, não uma nova fonte:

\[
Z_a(c,k)=\kappa^2\bigl[\kappa V_a(q_k,c)-h_0W_a(c)\bigr].
\]

`cubic_part_expansion` mantém o erro EXATO eventual

\[
\boxed{Z_a(c,k)=-h_1V_a(p3,c)+\delta^2V_a(\mathcal R_2(\delta),c).}
\]

`cubic_part_tendsto` conclui Z_a(c,k)→−h1 V_a(p3,c).
Tudo vale para qualquer input finito, sem hipótese de sinal.

`doubled_cubic_vector_identity` prova o fator 1/4 pela igualdade
(2k+2)^2=4(k+1)^2. Ele vem das duas escalas ORIGINAIS; não foi
selecionado para ajustar um coeficiente.

### 4. O teste dos nove cruzamentos fecha

`cubic_crossing_identity` transporta os dois erros VETORIAIS ao
pareamento original, com ambas as ordens presentes. `cubic_crossing_tendsto`
prova para TODOS os nove pares a,b:

\[
\boxed{\kappa\bigl(G_{ab}(k)-\kappa L_{ab}\bigr)\to B_{ab},}
\]

\[
\boxed{
B_{ab}=-\sqrt2h_1\left[
\tfrac14\langle C_a(E),V_b(p3,O)\rangle+
2\langle V_a(p3,E),C_b(O)\rangle\right].
}
\]

Cada G_ab é o cruzamento das componentes originais de J0(k),J1(2k+1).
Não se altera a forma assinada, a fonte ou o sentido da conjugação.
A subtração de κL_ab é uma identidade diagnóstica; não é usada para
substituir o pareamento físico bruto por um kernel ajustado.

`cubic_residual_row` e `cubic_residual_column` conservam os dois
cruzamentos ordenados com o complemento. `cubic_residual_residual_zero`
prova B22=0 pela identidade C2=0, já estabelecida no nível vetorial.
Isso não autoriza apagar o perfil cúbico residual não nulo −7u.

### 5. Recomposição independente pela Gram Cauchy original

`sum_cubic_eq` primeiro reconstitui os vetores completos. Então calcula

\[
\sum C(E)=\sum V(p3,E)=\phi_0,\qquad
\sum C(O)=i\phi_0-i\phi_1,\qquad
\sum V(p3,O)=i\phi_0-8i\phi_1.
\]

Na métrica Cauchy original, os dois pareamentos dão −13i/6 e i/6.
Consequentemente,

\[
\boxed{\sum_{a,b}B_{ab}
=-\sqrt2h_1\left[-13i/24+2i/6\right]
=\frac{5i\sqrt2}{24}h_1.}
\]

`recomposed_cubic_tendsto` obtém o limite da fonte completa pela soma dos
NOVE limites novos. `recomposed_green_cubic_tendsto` mantém a recomposição
Green original com bulk, ambos os bordos e o complemento.
O valor coincide com `doubledNext`, mas nenhum teorema escalar assintótico
anterior é usado como premissa para obter esse valor.

## C — O que foi refutado ou separado

O perfil residual cúbico não pode ser declarado ausente a partir de
residual–residual zero: ele é o vetor não nulo −7u, e seus dois cruzamentos
ordenados permanecem na fórmula. Não se afirma que esses cruzamentos
individuais sejam todos não nulos, nem que não possam cancelar.

A compensação (2^d u,v,(1−2^d)u) conserva a soma, mas não fornece sozinha
uma desigualdade para a forma canônica assinada. Positividade das normas
dos vetores separados não decide o sinal de seus cruzamentos.

Não se refutou a geometria Carry, a síntese completa ou a positividade
Hankel. Não foi construída uma nova métrica positiva para contornar a
obrigação. A ortogonalização da PR #41 e seus residuais permanecem com
o mesmo sentido lógico.

## D — O que permanece aberto

O teste cúbico foi concluído por componente e na soma. As duas leis
universais novas têm escopo preciso: Taylor em qualquer N para inputs
finitos, e compensação em qualquer grau de endereço no input E fixo.
Elas não provam um controle uniforme no número de jets, positividade
Hankel all-order, isometria entre regularizações ou operador infinito positivo.

O sinal de h1 não é uma hipótese das identidades e também não é uma
nova conclusão desta rodada. As fontes, endereços, duas pernas, fases,
amplitudes, retorno, Gamma, completion, métrica, pins e trabalhos antigos
foram preservados. Nenhum zero, altura ou momento ajustado foi usado
como entrada.

## E — Próximo passo mínimo

A lei par em qualquer grau agora permite testar a contribuição ÍMPAR antes
de estimar o balanço. Para O=i(e0−e1), a fórmula concreta a verificar no
mesmo domínio físico é

\[
V_2(p_d,O)=i\eta\left[(1-2^d)G_\eta\phi_1+
 (3^d-2^d)G_\eta\phi_2\right].
\]

Ela deve ser obtida do commutator original e confrontada com o bulk e os
DOIS bordos, preservando o cancelamento dos termos 3^d na reconstrução
completa. Esta fórmula ímpar geral NÃO foi formalizada nesta rodada.
O teste não requer calcular mais momentos nem pressupor seus sinais.

Só depois cabe buscar controle relativo dos cruzamentos completos em
inputs arbitrários. Uma lei de extração de coeficientes ou uma compensação
em um input fixo não substitui a desigualdade independente necessária
para os Schurs canônicos em toda ordem. Não extrapolar positividade a
partir dessas regressões e não rebatizar o próprio sinal como hipótese nova.

### Reprodução e validação

No host canônico llm, em checkout desta branch com o cache canônico:

```bash
cd research/native-cross-radial-green-cubic
python3 validate.py
```

O modo normal recompila os 57 ancestrais intactos da base. A opção
`--reuse-upstream` exige os hashes registrados de fontes E `.olean`.
Os quatro módulos novos e Audit são SEMPRE compilados explicitamente com
`lean -DwarningAsError=true`, além dos builds `lake build --wfail`,
auditorias Foundation/Geometry/Analysis e preservação de fontes/pins.

**Os 15 checks locais passaram com código de saída zero.** São 18
teoremas, duas definições e uma abreviação novas: 21 raízes públicas.
Todas têm `#print axioms` e inspeção transitiva de tipos E corpos:

| Grupo | Raízes | Dependências únicas | Controle |
| --- | ---: | ---: | --- |
| Construção/compensação | 6 | 5.138 | Momentos canônicos proibidos |
| Extração e recomposição | 15 | 5.750 | Mesma fonte, sem certificados de sinais |

Ambos os grupos bloqueiam os certificados de sinal h0/h1, consumidores
posteriores de positividade finita e os teoremas escalares da PR #110:
`first_cross_exact`, `doubled_first_exact`, `doubled_scaled_tendsto`,
`doubled_scaled_expansion`, `doubled_unscaled_expansion`,
`doubled_next_tendsto`. A recomposição não recebe como entrada o
coeficiente escalar que deveria explicar.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos na
análise; Foundation mantém suas regras próprias. Não se reivindica
footprint vazio para a análise. Nenhum `sorry`, `admit`, `native_decide`
ou axioma matemático novo foi introduzido.

`evidence/validation.json` registra comandos, logs e saídas;
`evidence/lean-Audit.log` e `public-roots.json` registram os certificados
e as raízes. `evidence/upstream.json` contém os hashes de fontes e `.olean`
dos 57 ancestrais recompilados. O bootstrap e seu registro conservam essa
compilação. `source-provenance.json`, `preservation.json` e `SHA256SUMS`
registram fontes, pins, arquivos antigos protegidos e integridade.
Quando necessário, espaços finais dos logs foram normalizados conservando
o bruto em `.raw.log.gz` com hash. Os resultados são locais; não se afirma
sucesso de CI remoto.

A publicação é draft sobre a PR #111, sem merge em main. O commit e a URL
ficam na entrega externa. A cópia local completa e seus hashes são
conferidos antes de remover apenas a worktree criada nesta rodada.

**Fim do relatório — PARTIAL para positividade all-order; coeficiente cúbico
nos nove cruzamentos, resto vetorial e compensação por grau de endereço preservados.**
