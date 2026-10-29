# Cancelamento completo dos setores TFVD na direção J₂−aJ₀

**Classificação: PARTIAL.** O alvo desta rodada é resolver a decomposição da
PR #93 na primeira direção par não constante: identificar os coeficientes
potencialmente divergentes do misto e de Green + bordo, provar seu cancelamento
e conservar a parte finita e o resto analítico. Isso não determina um sinal
Hankel em toda ordem.

Base: `35a1035eee70ebb2961b689a71b6d72ff46a41b3`, head da PR #94,
branch `agent/native-commutator-mixed-control`. A continuação está isolada em
`agent/native-critical-tfvd-cancellation`, com destino à PR #94, sem merge.
O operador original permanece em `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Main permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

A PR #41 separou ortogonalização algébrica de positividade e identificou o
residual de Schur com o bloco anterior invertível. Aqui, no primeiro bloco,
essa obrigação é somente `h₀≠0` para escolher `a=h₁/h₀`.

O limite da **soma inteira** em `J₂−aJ₀` já era conhecido:

\[
F(a)=h_2-2ah_1+a^2h_0.
\]

`research/critical-green-finite-part/FiniteExpansion.lean`, em particular
`CarryGreenFinitePart.green_balance_exact_expansion`, já obtinha uma expansão
mais profunda desse total. Não se reivindica esse limite nem o Taylor da
resposta como descoberta nova. Os adaptadores atuais usam os coeficientes
originais em `CompletedNativeTfvdWronskianMoments.lean` e extraem apenas o grau
necessário para resolver a decomposição atual.

A PR #93 provou, no espaço Cauchy físico original e com os dois traços,

\[
P_k(c)=P_G(c)+P_B(c)+P_C(c).
\]

A PR #94 demonstrou `A−AQ=κ=2i/√2`, identificou os dois comutadores com
`(2/√2)Cη[R]`, e conservou todos os seus cruzamentos na redução
`completed_kernel_mixed_reduction`. Um autopareamento nulo de `P_C` não permite
descartar esse componente. No primeiro jet, seu misto tinha sinal negativo,
usando explicitamente o sinal já certificado de h₀.

Os resíduos de decomposições históricas que distribuem o bordo de outra forma
não são identificados com `P_C` nesta rodada. O resultado abaixo diz respeito
precisamente aos três componentes da PR #93.

## B — Identidades e expansão dos setores

### B.1 — O vetor crítico é o original, antes do readout

Use `s=k+1`, `t=1/s`,

\[
d=(-1/2,1,-1/2),\quad e=(-1,0,0),\quad c_k(a)=s^2d+ae.
\]

São coeficientes de suporte `{0,1,2}`. `critical_source_jets`, em
`CriticalVectors.lean`, prova a igualdade do **par físico completo**

\[
\boxed{P_k(c_k(a))=J_2-aJ_0}.
\]

A escala `−s²/2` vem de `(2δ_k²)⁻¹`, com o passo radial original `δ_k=i/s`.
Não se escolheu uma amplitude para obter essa igualdade. Os J são os
`projectiveChiralDifferenceJet` existentes; não se troca sua fase pela da
matriz de coordenadas de bordo. As duas pernas e as quadraturas são mantidas.
O índice radial k não é profundidade vertical Carry.

`commutator_triple` conserva explicitamente os três coeficientes de saída:

\[
\begin{aligned}
(C_\eta[w](a,b,c))_1&=\eta^{-1}(w_2-w_1)c+\eta(w_0-w_1)a,\\
(C_\eta[w](a,b,c))_2&=\eta(w_1-w_2)b,\\
(C_\eta[w](a,b,c))_3&=\eta(w_2-w_3)c.
\end{aligned}
\]

O endereço 3 é necessário mesmo com entrada suportada abaixo de 3. Portanto,
regularidade e Taylor são conservados nos **quatro** endereços, sem truncar a
saída do stencil.

### B.2 — Dois fluxos da mesma resposta completada

Seja `S=physicalCauchySynthesis`, `R_k(j)` a resposta completada no endereço
`i(j+1)/s`, e `Gη=η M_u(I−ηM_u)⁻²` o Green já construído. Ponha

\[
\begin{aligned}
Q_k(c)&=\Re\mathfrak B(P_k(c),P_k(c)),\\
Z_k(c)&=\Re\{\mathfrak B(P_C(c),P_k(c))+
                  \mathfrak B(P_k(c),P_C(c))\},\\
B_k(c)&=\Re\mathfrak B((P_G+P_B)(c),(P_G+P_B)(c)).
\end{aligned}
\]

A métrica e a forma assinada originais permanecem
`𝔅(x,y)=(⟨x₊,y₊⟩−⟨x₋,y₋⟩)/2`. Depois de compor o par inteiro,
`full_response_flux` e `mixed_response_flux`, em `ResponseFlux.lean`, dão

\[
\boxed{Q_k(c)=2s\Im\langle Sc,S(D_{R_k}c)\rangle},\qquad
\boxed{Z_k(c)=2s\Im\langle Sc,G_\eta S(C_\eta[R_k]c)\rangle}.
\]

Essas identidades valem para todo suporte finito no domínio regular explícito,
sem usar os momentos canônicos ou seus sinais na construção. O segundo fluxo
já inclui os dois ordenamentos dos cruzamentos. O teorema polarizado da PR #94
precede esta especialização diagonal.

`full_split` conserva exatamente `Q=B+Z`. O fator 1/2 da forma não foi mudado:
o balanço literal das energias dos canais é `2Q`, e seu limite crítico é `2p`.

### B.3 — Os coeficientes espaciais são pareamentos físicos existentes

Escreva `p_r(j)=(j+1)^r` e defina as leituras

\[
\begin{aligned}
U_r&=\Re\langle Sd,G_\eta S(C_\eta[p_r]d)\rangle,\\
V_r&=\Re\{\langle Sd,G_\eta S(C_\eta[p_r]e)\rangle+
             \langle Se,G_\eta S(C_\eta[p_r]d)\rangle\},\\
W_r&=\Re\langle Se,G_\eta S(C_\eta[p_r]e)\rangle.
\end{aligned}
\]

Os monômios apenas extraem termos do Taylor da resposta original. Não são
outras fontes escolhidas para produzir positividade. `PhysicalKernels.lean`
implementa essas leituras e a versão sem comutador/Green, necessária para Q.
O parâmetro booleano escolhe entre essas duas expressões já identificadas;
não escolhe uma métrica, um modelo físico ou momentos alternativos.

Os três coeficientes do misto são, exatamente,

\[
\boxed{\begin{aligned}
A_4(\eta)&=2h_0U_1,\\
A_2(\eta,a)&=2ah_0V_1-2h_1U_3,\\
A_0(\eta,a)&=2a^2h_0W_1-2ah_1V_3+2h_2U_5.
\end{aligned}}
\]

São `poleFour`, `poleTwo` e `finitePart` para o setor misto. Nenhum sinal foi
atribuído a esses coeficientes.

### B.4 — Cancelamento exato antes de interpretar a parte finita

Existe um resto analítico R da resposta completada, comum aos dois setores, tal que

\[
-iR_{\rm native}(it)=h_0t-h_1t^3+h_2t^5+t^7R(t).
\]

`response_weight_taylor` conserva essa identidade nos quatro endereços.
`sector_flux_exact_expansion` e `complete_tfvd_expansion` provam, eventualmente,
para cada `a` livre e cada `0<η<1`,

\[
\boxed{\begin{aligned}
Z_k(c_k(a))&=s^4 A_4+s^2 A_2+A_0+t^2E_C(t),\\
B_k(c_k(a))&=-s^4 A_4-s^2 A_2+\{F(a)-A_0\}
                 +t^2\{E_Q(t)-E_C(t)\},\\
Q_k(c_k(a))&=F(a)+t^2E_Q(t).
\end{aligned}}
\]

As funções E são definidas pelos mesmos quatro valores de R e pelos operadores
originais. São contínuas em zero. O cancelamento de cada coeficiente de ordem
s⁴ e s² é uma igualdade, não um argumento de que duas parcelas pequenas podem
ser negligenciadas. Não se afirma que A₄ ou A₂ sejam não nulos: sem isso não se
deve anunciar divergência estrita dos setores.

`full_spatial_constants` computa na Gram Cauchy original os cancelamentos do
fluxo inteiro: U₁=V₁=U₃=0, W₁=1/2, V₃=1, U₅=1/2 para esse fluxo. Daí surge
exatamente F(a). Não se ajusta o Green nem a fonte para obter as constantes.

`sector_second_order_error_bound` fornece um M positivo e um limiar eventual
para o erro de cada fluxo após retirar seus termos s⁴, s² e constante:

\[
|\text{erro}|\le M/s^2.
\]

M pode depender da fonte, de η e de a. Não há cutoff numérico, controle uniforme
em todas as ordens ou estimativa relativa a um pivô positivo desconhecido.

### B.5 — Partes finitas e a ligação exata com a PR #41

`mixed_renormalized_limit` e `bulk_boundary_renormalized_limit` dão

\[
Z_k-s^4A_4-s^2A_2\to A_0,\qquad
B_k+s^4A_4+s^2A_2\to F(a)-A_0.
\]

Só depois se escolhe `a=h₁/h₀`. Com apenas `h₀≠0`,
`critical_tfvd_named_schur_limit` identifica o limite de Q com o mesmo
`sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1` da PR #41:

\[
F(h_1/h_0)=h_2-h_1^2/h_0.
\]

Isso não usa a positividade do novo pivô. O sinal desse pivô já tinha outros
certificados; a contribuição aqui é resolver os setores TFVD atuais que o
recompõem, sem confundir o residual algébrico com uma norma positiva.

## C — O que não é uma consequência válida

Não se pode usar o limite negativo do misto do primeiro jet, na PR #94, para
atribuir o mesmo comportamento ao segundo: aqui há coeficientes s⁴ e s² a
considerar antes da parte finita.

Não se pode usar `𝔅(P_C,P_C)=0` para remover Z, nem inferir o sinal da soma do
sinal isolado de qualquer setor. Não se pode identificar um dos termos finitos
com o pivô inteiro, pois eles somam A₀ e F−A₀.

Estas observações não constituem um NO-GO da geometria, nem uma prova de pivô
negativo. Não se modificou a estrutura para contornar um sinal inconveniente.

## D — Alcance e auditoria

A construção vetorial e as identidades físicas são separadas da identificação
analítica dos coeficientes canônicos. Nenhum teorema novo consome sinal de h₀,
de outros momentos ou de Hankel. A escolha crítica recebe somente h₀≠0.
Os resultados de positividade finita anteriores permanecem intactos e não são
premissas destes teoremas.

Os resultados novos se referem a esta direção de três endereços. As identidades
de fluxo valem para suporte finito arbitrário, mas a expansão de setores ainda
não é um teorema em toda ordem de jet. A síntese original conserva a cauda física;
não se introduziu cutoff adicional na variável física u nem se aproximou G.
Não se resolveu o domínio infinito dos multiplicadores completados A e AQ.

`Audit.lean` executa `#print axioms` e percorre transitivamente tipos e corpos,
incluindo auxiliares privados. O grupo físico rejeita dependência da sequência
canônica; ambos os grupos rejeitam os certificados de sinal selecionados e os
consumidores posteriores de positividade. Os únicos axiomas permitidos são
`propext`, `Classical.choice` e `Quot.sound`. Não há `sorry`, `admit`,
`native_decide` ou novos axiomas matemáticos.

São 57 teoremas, 25 definições e uma abreviação públicos, incluindo os
adaptadores das identidades de Taylor e Schur anteriores identificados acima.

| Grupo auditado | Raízes públicas | Dependências transitivas de tipos/corpos |
| --- | ---: | ---: |
| Construção e identidades físicas, sem sequência canônica | 43 | 5.536 |
| Identificação dos coeficientes, sem seus sinais | 40 | 5.967 |

Os totais transitivos se sobrepõem e não devem ser somados.

Os comandos e resultados efetivos ficam em `evidence/validation.json`; os hashes
da fonte, pins e trabalhos antigos protegidos, em `source-provenance.json` e
`preservation.json`. `build_upstream.py` recompila somente os treze ancestrais
da PR #92 à #94 realmente usados, verificando sua igualdade com a base.
Os módulos de pesquisa e Audit são compilados explicitamente com warnings como
erros; a raiz Lake sozinha não os inclui. O procedimento também executa
`lake build --wfail` e as auditorias Foundation, Geometry e Analysis.
Nesta execução, **os 17 comandos passaram com código de saída zero**, assim
como as verificações finais de preservação de fontes, pins e trabalhos antigos.
`MANIFEST.sha256` permite verificar os arquivos entregues com
`sha256sum -c MANIFEST.sha256` nesta pasta.

## E — Próxima obrigação mínima

A decomposição deixou de esconder a parte finita: agora é possível investigar
os pareamentos espaciais U, V e W diretamente no Green físico original.
O próximo teste concreto é fatorar **U₁** da curvatura d, preservando seu bordo,
e determinar seu sinal a partir dos multiplicadores `M_u` e `(I−ηM_u)⁻¹`, sem
theta ou positividade canônica. Isso dirá se o primeiro termo potencialmente
divergente é efetivo e por que seu oposto aparece em Green + bordo.

Uma obrigação concreta para a próxima rodada é verificar e formalizar a candidata

\[
U_1\stackrel{?}=\tfrac14\bigl(\|v\|^2-\eta^2\|(I-M_u)v\|^2\bigr),
\qquad v=(I-\eta M_u)^{-1}(\phi_1-\phi_2).
\]

Ela não é um teorema do certificado atual. Se a identidade e a contratividade de
`I−M_u` forem certificadas no mesmo domínio, o sinal de U₁ poderá vir de uma
diferença de normas controlada, sem receber um sinal de Hankel como hipótese.

Para avançar em toda ordem, deve-se então testar a mesma identidade espacial
nos stencils nativos de ordem arbitrária. Uma lei de cancelamento dos termos
divergentes não é, por si só, uma lei de sinal do residual finito. A obrigação
principal continua sendo uma identidade ou desigualdade independente da fonte
que determine o sinal da **soma finita completa**, com o mesmo kernel.

Reprodução no servidor `llm`, na pasta desta investigação:

```bash
python3 validate.py
```

A entrega permanece em branch e PR draft identificadas, sem merge automático.
Fonte, pesos, amplitudes, métrica, pins, main e trabalhos antigos são preservados.

**Fim do relatório.**
