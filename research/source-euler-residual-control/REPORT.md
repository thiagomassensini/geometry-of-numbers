# Controle assinado do residual da fonte — continuação da PR #48

**Classificação: PARTIAL.** A extração de Euler foi transportada, em toda ordem e com dois argumentos independentes, para o orçamento físico da PR #48 e para as direções residuais exatas da PR #41. Um teste da fonte original prova que o resto não linear pode ser negativo enquanto o orçamento completo conserva uma margem positiva. A positividade canônica em toda ordem permanece aberta.

Base desta branch: `9bcec6bd0b3809f46a0fcb2e5a284bf21152713a`, HEAD da PR #48 (`agent/native-jet-overlap-budget`). Branch: `agent/source-euler-residual-control`. A continuação depende das PRs #46/#47/#48 e consulta fontes imutáveis das PRs #34 e #41; não presume que estejam integradas à `main`. Não há merge automático.

## A — O que já estava demonstrado

A PR #41, no commit `ee56930a2c30456cfbd214a29bb31b12d3977204`, constrói `orthogonalPolynomial`, `nativeResidualBoundary` e sua energia por eliminação algébrica. `nativeResidualBoundary_energy` identifica a energia original com quatro vezes `carryPairingPivot`, sem hipótese de sinal ou inversibilidade. A efetiva ortogonalidade aos graus anteriores exige os pivôs anteriores não nulos. A versão por inversa, `native_inverseSchur_boundary_energy`, recebe somente a inversibilidade do bloco antigo.

A PR #48 prova, para os mesmos coeficientes originais `nativeSourceChiralJetInput`,

\[
\mathcal Q_k(x,y)=P_k(x,y)+\Delta_k(x,y),\qquad P_k(x,x)\ge0.
\]

Os nomes reutilizados são `jetBudget_eq_damped_add_defect`, `dampedCameraBalance_self_nonneg`, `pr41_residual_budget_eventually_close` e `pr41_inverseSchur_budget_eventually_close`. O limite canônico é o limite da soma; não se identifica o defeito físico `Delta` com o pivô algébrico.

No operador original, `radialCompletedSlopeSynthesis_eq_euler_add_remainder` separa o vetor de inclinações da fonte em contribuição de Euler e resto completo. `radialEuler_boundary_polarized` calcula os dois cruzamentos da contribuição de Euler. `storage_one_eq_euler_boundary_add_remainder` mantém o pareamento do resto na métrica Cauchy original. Essas identidades já existiam: o avanço desta rodada é sua extração no orçamento da #48 e nas direções da #41, em ordem arbitrária.

A PR #43 havia certificado um resto não linear positivo na segunda direção crítica par. Isso não era uma lei de sinal para todas as ordens. O candidato testado aqui foi precisamente a extensão desse mecanismo.

As caixas da fonte e a coluna racional do teste adicional vêm da PR #34, commit `da58f044c1c75bd828951bfb41614a6e7b8b465e`. `prepare_pr34.py` extrai e recompila somente os sete módulos de coeficientes, recorrência e caixas, até `EvenTrialData`; não importa `EvenSeventhCertificate`. A PR #34 corresponde à investigação da issue #32. Seu certificado de sétimo pivô não foi refeito nem usado para fornecer o sinal dos novos resultados.

Os blocos H6/K6 e a realização de doze fontes já certificados permanecem regressões. Sua positividade finita não é premissa para o novo resultado estrutural em toda ordem.

## B — O que foi demonstrado agora

### B.1 — Extração da parcela de Euler da própria fonte

Seja `d_x = jetValues n k x`, isto é, o resultado do mapa de coeficientes original seguido de `radialCompletedValueCoefficients`. Os vetores usados abaixo são literalmente

\[
V_x=\operatorname{radialIncidentSynthesis}(d_x),\qquad
R_x=\operatorname{radialCompletedRemainderSynthesis}(d_x).
\]

`R_x` é o resto do companheiro completado; não é o canal retornado da decomposição incidente–retorno. Tampouco é o defeito físico `Delta` da PR #48. Esses três objetos têm papéis diferentes.

Definimos apenas o nome do pareamento já existente:

\[
\mathcal N_k(x,y)=\langle V_x,R_y\rangle+
                         \langle R_x,V_y\rangle,
\qquad
N_k(x)=4\operatorname{Re}\langle V_x,R_x\rangle.
\]

`nonlinearPairing_self_re` prova `Re Ncal(x,x) = N_k(x)/2`. Nenhuma contribuição analítica do companheiro foi descartada.

`forward_weights_sum` e `jet_values_sum` provam, antes da leitura quadrática,

\[
\sum_r d_x(r)=\frac{x_0}{\sqrt2}.
\]

Isso ocorre porque a diferença finita mata a constante em toda ordem positiva, com os pesos e as fases originais. Os fatores `F` e `E+` são cancelados exatamente onde os teoremas de regularidade os provam não nulos. O fator `1/sqrt(2)` não é uma normalização nova.

`euler_scale_native` identifica a escala diretamente pela curvatura da característica completada:

\[
\operatorname{EulerScale}_k=\frac{2h_0}{k+1}.
\]

Sua prova usa `canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral`, sem desigualdade theta ou positividade de Hankel.

### B.2 — Dois argumentos independentes e aplicação à PR #41

`budget_slope_polarized` aplica as identidades de síntese completa aos dois argumentos independentes. `budget_euler_polarized` conclui

\[
\boxed{\mathcal Q_k(x,y)=h_0\overline{x_0}y_0+\mathcal N_k(x,y).}
\]

Os dois pareamentos mistos ordenados aparecem explicitamente. A fórmula diagonal `budget_euler_exact` é

\[
\boxed{\operatorname{Re}[P_k(x,x)+\Delta_k(x,x)]
       =h_0|x_0|^2+\frac12N_k(x),}
\]

onde a igualdade diagonal considera as partes reais. As hipóteses são apenas o strip físico e a não anulação dos fatores originais nos nós, disponíveis eventualmente para cada dimensão fixa. Não há hipótese de contratividade, sinal de pivô ou representação positiva dos momentos.

`nonlinear_tendsto` prova, para toda entrada finita fixa,

\[
N_k(x)\longrightarrow
\frac12\operatorname{nativeSourceFiniteBoundaryEnergy}(x)-2h_0|x_0|^2.
\]

Aplicando literalmente `nativeResidualBoundary s n`, `pr41_nonlinear_tendsto` dá

\[
\boxed{N_k(x_{s,n})\longrightarrow 2d_{s,n}-2h_0|(x_{s,n})_0|^2.}
\]

É o mesmo residual algébrico da PR #41, sem novo produto interno, nova fonte ou coeficientes físicos escolhidos a partir de uma Gram positiva.

`pr41_even_euler_coefficient` e `pr41_odd_euler_coefficient` separam os setores:

\[
|(x_{0,n})_0|^2=p_n(0)^2,\qquad |(x_{1,n})_0|^2=0,
\]

com `p_n = orthogonalPolynomial h n`. No par existe a parcela `h0*p_n(0)^2`; no ímpar, a contribuição de Euler é exatamente nula. Logo ela não explica sozinha o sinal de ambos os setores.

A primeira dessas parcelas só é estritamente positiva quando o coeficiente constante for não nulo. Não introduzimos essa não degenerescência como se já estivesse provada em toda ordem.

### B.3 — Cota relativa concreta permitindo um resto negativo

O teste usa a coluna seis de `CarrySeventhEven.trialCoefficient`, com sua escala original. Não altera a fonte: escolhe uma entrada racional já existente para o mapa físico original. Denotando esse polinômio por `q`, `seventh_trial_energy` prova

\[
\operatorname{nativeSourceFiniteBoundaryEnergy}(q)=4\,\mathcal B_h(q,q).
\]

As caixas, com todas as contribuições da fonte e todos os cruzamentos, dão os novos certificados

\[
\boxed{-\frac25<\mathcal B_h(q,q)-h_0q(0)^2<-\frac15,}
\qquad
\boxed{\mathcal B_h(q,q)>5.}
\]

Nomes: `seventh_nonlinear_mem`, `seventh_nonlinear_checks`, `seventh_nonlinear_bounds`, `seventh_trial_positive_margin`. As comparações racionais são reduzidas pelo kernel (`decide +kernel`); não usam os valores pontuais do checkpoint nem a positividade do sétimo pivô.

`seventh_nonlinear_tendsto` transporta essas desigualdades para o pareamento físico completo. `seventh_signed_compensation` prova, eventualmente e na mesma entrada,

\[
\boxed{N_k(q)<0,\qquad \operatorname{Re}[P_k(q,q)+\Delta_k(q,q)]>5.}
\]

Em particular, esta é uma instância rigorosa da cota de subtração pedida pela #48:

\[
\operatorname{Re}\Delta_k(q,q)>-\operatorname{Re}P_k(q,q)+5.
\]

A constante 5 é uma margem inferior certificada para a entrada racional herdada; não foi adicionada à fonte nem escolhida como altura ou momento. A coluna herdada tem coeficiente líder `10^20`; na versão mônica, o mesmo resultado se expressa pela margem `5*10^(-40)`, por homogeneidade das mesmas formas. Não reivindicamos nesta rodada um teorema novo de covariância: a escala foi preservada exatamente no Lean.

## C — O que foi refutado e limites do teste

A afirmação de que o resto não linear completo é não negativo em todas as entradas nativas é falsa: `seventh_nonlinear_eventually_negative` fornece uma entrada da própria fonte. A compensação assinada precisa ser mantida. A positividade observada na #43 não se estende dessa maneira a toda a fonte.

Isso não refuta a positividade da Hankel canônica. O MESMO teste prova uma margem positiva para o orçamento completo. Também não prova que `Delta` é negativo nessa entrada: o teorema de sinal aqui é sobre `N`, o resto do companheiro, e não sobre o defeito de transporte da #48.

A coluna racional `q` é uma aproximação da direção residual da sétima ordem; não declaramos que ela seja exatamente o polinômio mônico da #41. Portanto, a obstrução formal acima é à não negatividade em TODAS as entradas. Não é anunciada como uma obstrução já formalizada ao sinal de `N` apenas nas direções residuais canônicas exatas.

Como teste separado, `checkpoint_probe.py` resolve `Ax=b` usando somente a coluna histórica `canonical_h` do Stage A, sem nova avaliação da característica e sem usar zeros ou alturas. Repetiu 31 direções pares, a 300 e 450 DPS, concordando em 32 dígitos nas razões reportadas. O primeiro resto negativo aparece no índice `n=6`:

- pivô aproximadamente `5.13686428e-40`, positivo;
- metade do resto aproximadamente `-2.56642652e-41`, negativo;
- razão `(d_n-h0*p_n(0)^2)/d_n` aproximadamente `-0.04996095644`.

Esses números são diagnóstico dos decimais armazenados. Não são intervalos certificados dos momentos verdadeiros. O certificado Lean de B.3 usa as caixas independentes da fonte original. Não se transfere automaticamente a ele o enunciado sobre a direção crítica exata do diagnóstico.

## D — O que está no kernel e o que permanece aberto

São 24 teoremas e 6 definições novos, em três módulos: `ResidualEuler`, `PolarizedEuler` e `SourceWitness`. O inventário de raízes está em `public-roots.json`; a auditoria imprime os axiomas de cada uma e percorre transitivamente tipos e corpos. A separação é entre núcleo estrutural e teste finito de fonte.

A auditoria final verificou 16 raízes estruturais, com 6.753 constantes transitivas, e 14 raízes do teste de fonte, com 6.652 constantes. Todos os 31 checks terminaram com código de saída zero, incluindo os builds `--wfail`, as três auditorias e a regressão de doze fontes.

Os dois grupos rejeitam dependência dos certificados nomeados de positividade H6, K6, sétimo pivô e contratividade de sete fontes. O grupo estrutural também rejeita os comparadores finitos centrais nomeados da sequência. Os únicos axiomas permitidos são `propext`, `Classical.choice` e `Quot.sound`.

A prova estrutural não começa na theta. O teste numérico não é premissa Lean. O teste finito de sinal B.3 reutiliza explicitamente caixas theta já certificadas da MESMA fonte, com suas caudas e a recorrência completada; esse uso é um certificado de desigualdade finita, não uma representação Gram all-order nem uma substituição da síntese física.

Continuam abertos:

1. Uma estimativa independente dos canais que controle `N_k` em toda direção residual canônica, com margem que não receba o pivô desconhecido como entrada.
2. A positividade em toda ordem dos dois setores canônicos.
3. A realização positiva infinita coerente, com a mesma fonte e o mesmo kernel.

Nem a extração de Euler nem a ortogonalização algébrica da #41 descarregam essas obrigações. No setor ímpar, a extração deixa todo o sinal no pareamento não linear. No par, um resto negativo ainda pode ser permitido, mas sua magnitude precisa ser controlada em relação ao termo de Euler.

### Reprodução e preservação

```bash
cd /home/thlinux/geometry-of-numbers
git fetch origin ee56930a2c30456cfbd214a29bb31b12d3977204
git fetch origin da58f044c1c75bd828951bfb41614a6e7b8b465e
python3 research/source-euler-residual-control/validate.py
```

Os fetches disponibilizam os objetos imutáveis; não fazem merge. A #41 é recompilada pelo procedimento herdado da #48. Os sete módulos da #34 são extraídos byte a byte com hashes em `evidence/pr34-source.json`. Não entram fontes de `EvenSeventhCertificate`.

A validação recompila as dependências de transporte necessárias, as provas novas, executa `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e a regressão H6/K6/doze fontes. Os logs vivos são mantidos fora do checkout, para que a auditoria de whitespace não leia arquivos parcialmente escritos. Comandos, resultados e hashes das fontes ficam em `evidence/checks.json` e `evidence/source-sha256.json`.

Não foram alterados fontes históricas, métricas, amplitudes, fases, dressing, completion, normalizações, pins ou branches das PRs anteriores. Os dois arquivos não rastreados do operador permanecem preservados. A alteração inteira fica neste novo diretório de pesquisa.

## E — Próximo passo mínimo e conclusão

A recomendação da #48 foi executada como investigação de uma cota da fonte: obtivemos a extração polarizada em toda ordem e uma cota relativa estrita na entrada racional testada, permitindo que o resto não linear seja negativo. A hipótese mais simples de sinal universal do resto foi refutada para entradas gerais da própria fonte.

Para as direções exatas da #41, o menor controle agora pode ser enunciado no pareamento físico efetivo `N_k`. No par, é necessário demonstrar uma margem depois de permitir sua parte negativa; no ímpar, Euler não oferece uma reserva positiva. Apenas assumir essa margem seria receber novamente a positividade desejada, e não foi feito aqui.

Um teste curto antes de procurar uma lei universal é transportar o controle intervalar da coluna racional `q` à direção residual EXATA `nativeResidualBoundary 0 6`: provar uma cota para sua diferença no pareamento não linear, usando a inversibilidade já certificada do prefixo e mantendo todos os coeficientes. Isso decidiria formalmente se a mudança de sinal sugerida pelo checkpoint ocorre nessa própria direção. Não é necessário recalcular o sétimo pivô ou aumentar milhares de momentos.

Para avançar além do teste finito, ainda falta uma desigualdade da dinâmica/retorno que limite a parte negativa desse pareamento nas direções residuais, sem ser definida a partir do sinal do pivô. A identidade nova localiza esse termo, mas não constitui tal lei em toda ordem.

**Resposta principal:** a fonte fornece uma compensação assinada verificável, inclusive com resto negativo. Esta rodada não demonstra que suas relações já provadas obriguem todos os pivôs canônicos a serem positivos. Resultado `PARTIAL`; não há conclusão all-order nem NO-GO da geometria Carry.
