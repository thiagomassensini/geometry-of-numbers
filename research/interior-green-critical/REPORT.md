# Portas interiores do TFVD e direção crítica par da PR #41

**Classificação global: PARTIAL.** O alvo local demonstrado é a fórmula vetorial das portas interiores e seu transporte para a direção crítica original J₂−(h₁/h₀)J₀. Não se presume o sinal de um novo pivô.

Base imutável: `ba5b0a30c7b299f994918db7b9f642c5c7d78850`, PR #85, draft. Branch desta continuação: `agent/interior-green-critical`; base de revisão: `agent/first-odd-green`. Main e as PRs anteriores permanecem intactas. Sem merge automático.

## A — O que já estava demonstrado

A PR #41 separou a existência da ortogonalização algébrica do sinal dos residuais. Seus teoremas `NativeMomentOrthogonalization.sourceMomentSchur_sewing_of_isUnit` e `sourceMomentSchur_critical_direction_of_isUnit` recebem inversibilidade do bloco antigo, não positividade do novo pivô. A energia de bordo antiga lê quatro vezes o Schur; esse fator não é alterado aqui. A draft #41 permanece independente: esta continuação reutiliza a definição original `CarrySelfAdjointOperator.sourceMomentSchur`, não importa nem modifica os arquivos da draft.

As PRs #81/#82 demonstraram o refinamento físico isométrico comum, o kernel polarizado com dois índices radiais independentes e a reconstrução Green vetorial completa. Reutilizamos `physical_jet_original`, `common_even_jets`, `refined_source_green_split`, `physical_form_four_sectors`, `form_same_power`.

As PRs #84/#85 extraíram as duas primeiras portas e a primeira diferença ímpar original, mantendo as duas pernas e os cruzamentos. Reutilizamos `residual_basis_pair`, `reconstructed_residual_initial`, `reconstructed_successor`, `basis_contrast`, `numerator_smul_sub` e as portas Green físicas antigas.

H6/K6 e as realizações positivas finitas anteriores não são premissas das novas identidades. Também não se recebem zeros, alturas, uma medida positiva presumida, whitening ou novos pesos.

## B — O que foi demonstrado agora

### Notação e objeto físico

κ=k+1 é a escala da regularização radial, não profundidade Carry. δ=i/κ e zⱼ=(j+1)δ. A resposta continua R=−F′/(2F), da característica completada original. As colunas são as antigas φⱼ(x)=√x·xʲ no fechamento físico Cauchy. A, Gη e αₖ=√(2κ) são o avanço, o resolvente e a amplitude antigos. O parâmetro Green satisfaz 0<η<1 quando invocamos a reconstrução física.

A forma antiga é assinada:

\[
 \Phi(u,v)=\tfrac12(\langle u^+,v^+\rangle-\langle u^-,v^-\rangle).
\]

Não se confunde essa diferença com a norma positiva de uma única perna. Definimos ΔRⱼ=R(zⱼ₊₁)−R(zⱼ), somente como abreviação da fonte.

### Fórmula interior, em todo endereço

`interior_bulk` e `interior_numerator` provam, para todo j≥0:

\[
 B_ηe_{j+2}=η^{-1}e_{j+1}-2e_{j+2}+ηe_{j+3},
 \qquad
 N_ηe_{j+2}=η^{-1}\mathcal E_{j+1}-ηA\mathcal E_{j+2}.
\]

São identidades algébricas sem hipótese de sinal. O termo anterior não é descartado. Com as condições originais de não anulação nos três nós necessários e η≠0, `reconstructed_interior` identifica exatamente

\[
 \widehat E_r=(α_kV_r,α_kV_r),\qquad r\ge2,
 \qquad V_r=\Delta R_{r-1}G_η^2φ_r-η^2\Delta R_rG_η^2φ_{r+2}.
\]

Nos dois endereços de bordo, permanecem as fórmulas anteriores:

\[
 V_0=\Delta R_0P_η,\quad P_η=ηG_η^2(2φ_1-ηφ_2),
 \qquad
 V_1=\Delta R_1Q_η,\quad Q_η=-η^2G_η^2φ_3.
\]

A identidade é vetorial no espaço físico anterior. Não é uma porta definida de um momento ou de um pareamento desejado.

### Síntese fechada para toda entrada finita

`residual_basis_all` reúne os três regimes, sem identificar o bordo com o interior. `finite_residual_closed` prova, para qualquer entrada complexa x de suporte finito:

\[
 \widehat E_k(x)=(W_k(x),W_k(x)),
 \qquad W_k(x)=\sum_{j\in\operatorname{supp}x}x_jα_kV_j.
\]

Essa é a reconstrução residual antiga inteira. `residualMap` apenas fornece sua estrutura linear já demonstrada; `bulkMap` é identificado com o bulk antigo por `bulk_map_original`, no domínio 0<η<1. Nenhum operador, métrica ou fonte é ajustado.

As hipóteses locais são F(zᵢ)≠0 e E⁺(zᵢ)≠0 em prefixos finitos associados ao suporte. `finite_prefix_eventually` descarrega essas hipóteses para cada entrada finita fixa a partir do germe original; `finite_residual_eventually_closed` não recebe regularidade global como axioma.

`finite_residual_cross_zero` mantém duas entradas complexas e dois índices radiais independentes. Prova EE=0 depois de identificar as duas pernas. Isso não afirma W=0 e não autoriza eliminar BE ou EB.

### Mesma direção crítica, nove cruzamentos

O coeficiente a é inicialmente livre. Se ν=(2δ²)⁻¹, então

\[
 c_0=ν-a,\qquad c_1=-2ν,\qquad c_2=ν,
 \qquad S_k(c)=J_2(k)-aJ_0(k).
\]

`critical_source_original` verifica o fatorial 2, a fase complexa e a igualdade com os jets físicos anteriores. A família J já existe antes de escolher a. A posterior escolha a=h₁/h₀ é a direção algébrica da PR #41; não fabrica estados para definir uma Gram positiva.

`three_ordered_crossing` extrai todas as nove entradas originais:

\[
 \Phi(\widehat B_i,\widehat E_j)
 =-iκ\langle φ_i,V_j\rangle,\qquad i,j\in\{0,1,2\}.
\]

`critical_mixed_nine_crossings` preserva a conjugação de cada coeficiente e todos os termos:

\[
 \Phi(B_a,E_b)=\sum_{i,j=0}^2\overline{c_i(a)}c_j(b)
             \Phi(\widehat B_i,\widehat E_j).
\]

`critical_vector_split`, `critical_residual_pair` e `critical_energy_three_sectors` identificam, nessa ordem, os vetores, o residual inteiro e só então a leitura real:

\[
 \Re\Phi(J_2-aJ_0,J_2-aJ_0)=\Re\Phi(B_a,B_a)+2\Re\Phi(B_a,E_a).
\]

### Polarização e Schur original

`critical_pairing_four` e `critical_pairing_limit` mantêm dois índices radiais independentes e dois coeficientes a,b independentes, após os refinamentos isométricos já provados. O limite complexo é

\[
 h_2-(a+b)h_1+ab h_0.
\]

A diagonal é uma consequência desse teorema polarizado. `first_source_schur_eq` identifica a definição original `sourceMomentSchur m 0 1` com m₂−m₁²/m₀, inclusive na convenção total do inverso. `schur_green_limit`, recebendo somente h₀≠0, prova

\[
 \Re\Phi(B_{h_1/h_0},B_{h_1/h_0})
 +2\Re\Phi(B_{h_1/h_0},E_{h_1/h_0})
 \longrightarrow\operatorname{sourceMomentSchur}(h,0,1)
 =h_2-\frac{h_1^2}{h_0}.
\]

Portanto, a reconstrução Green completa recupera o mesmo Schur da ortogonalização, com a normalização de Φ já existente. Não o transforma numa norma positiva. `critical_limit_complete_square` registra explicitamente o resíduo algébrico e o termo h₀(a−h₁/h₀)²; o sinal do primeiro não vem dessa identidade.

### Validação

Os quatro módulos novos são `InteriorPorts.lean`, `CriticalEvenPorts.lean`, `FinitePorts.lean` e `CriticalKernel.lean`. Há 38 teoremas e 14 definições (52 raízes públicas), todas no namespace `CarryInteriorGreen`. Os nomes principais estão associados às identidades acima; `Audit.lean` contém `#print axioms` para cada raiz e uma inspeção transitiva de tipos e corpos, incluindo constantes privadas.

A auditoria produziu:

| Grupo | Raízes | Dependências únicas de tipos/corpos | Controles |
| --- | ---: | ---: | --- |
| Construção física | 39 | 5895 | Proíbe definir os estados pelos momentos canônicos e bloqueia consumidores finitos posteriores. |
| Identificação e limites | 13 | 6294 | Admite a sequência original; bloqueia certificados de sinal finito e polinômios theta como premissas. |
| União | 52 | 6343 | Somente `propext`, `Classical.choice`, `Quot.sound`; sem novos axiomas matemáticos. |

**PASS nos 15 comandos registrados:** proveniência, geração da auditoria, build focado dos módulos nativos com `lake build --wfail`, compilação explícita dos quatro módulos novos e de `Audit.lean` com avisos tratados como erros, diagnóstico 80/120 dígitos, build raiz com `--wfail`, auditorias Foundation/Geometry/Analysis, preservação da base e `git diff --check`.

Sem `sorry`, `admit`, `native_decide` ou novos axiomas nas fontes. Fonte, métrica, fases, amplitudes, bordos, completion, pins e módulos históricos foram preservados. Os dois arquivos não rastreados preexistentes no operador tiveram seus hashes conferidos. O build raiz não importa automaticamente os módulos de pesquisa: eles foram compilados e auditados explicitamente antes dele.

A draft #41 foi conferida aberta e independente, head `ee56930a2c30456cfbd214a29bb31b12d3977204`. Seus arquivos não foram modificados nem apresentados como recompilados nesta execução.

Reprodução no host canônico llm, em checkout desta branch com as dependências preservadas:

```bash
cd /home/thlinux/geometry-of-numbers-interior-green-critical/research/interior-green-critical
mkdir -p evidence
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

Os 29 módulos ancestrais foram recompilados a partir das fontes imutáveis da base. `record_provenance.py` compara os hashes com o commit base e registra os `.olean`, módulos nativos, pins e PRs. `validation.json` registra comandos, saídas e os hashes das fontes novas.

O diagnóstico Python foi executado a 80 e 120 dígitos. Avalia F pela identidade downstream já provada com a característica xi, sem reexecutar toda a síntese material TFVD e sem ler zeros, alturas ou tabelas de momentos. Confere os nove cruzamentos físicos separadamente, suas fases e coeficientes, e a recomposição do balanço inteiro para κ=10,100,1000. O pivô diagnóstico é aproximadamente 8,43685841013415×10⁻⁸. Esses números e a taxa κ⁴ sugerida para parcelas separadas não são novos teoremas de sinal ou assintótica desta PR.

## C — Defeitos e tentativas que não são provas

A versão que apaga o termo anterior no numerador interior tem defeito exato η⁻¹Eⱼ₊₁. Não se provou aqui que esse vetor seja não nulo em todo ponto; tampouco se pode apagá-lo sem provar seu anulamento. Os casos e₀ e e₁ continuam excepcionais e não recebem o stencil interior por deslocamento.

EE=0 decorre da isotropia da forma assinada, não de redundância física nem de fonte nula. O novo termo anterior contribui nos cruzamentos mistos.

A identidade com Schur não é prova do seu sinal. Concluir positividade porque a operação foi denominada ortogonalização repetiria a inversão lógica auditada na PR #41. Não foi demonstrado um NO-GO da geometria, nem uma representação Gram positiva nova.

## D — O que permanece aberto

O alvo local passa a ter uma fórmula de portas em todos os endereços e uma síntese explícita para toda entrada finita, com as condições de domínio identificadas e descarregáveis para cada suporte fixo. Não foi provada uma estimativa uniforme na ordem nem uma lei de sinal para os Schurs canônicos arbitrários.

O teste numérico do segundo par positivo não é uma nova prova Lean de positividade. A positividade desse pivô e de prefixos maiores já tinha certificados finitos por outras rotas; não os usamos para definir as portas, inferir o limite ou ocultar o sinal restante.

A obrigação principal continua sendo uma desigualdade independente da fonte para o balanço completo na direção crítica, incluindo todos os termos que sobrevivem depois dos cancelamentos. Os vetores físicos estão identificados; o sinal não é consequência automática da norma de cada perna.

## E — Próximo passo mínimo

Usar a fórmula fechada Vⱼ para desenvolver diretamente o balanço completo da direção crítica, com todos os nove cruzamentos, até o primeiro termo finito. O diagnóstico sugere parcelas separadas de ordem κ⁴; essa taxa não foi formalizada nesta continuação. Uma expansão deve derivar os cancelamentos dos termos divergentes e controlar o resto analítico da mesma resposta R, sem alterar a fonte ou introduzir uma energia renormalizada como substituta.

A propriedade nova procurada deve controlar o termo finito original independentemente de se supor o sinal do Schur. Provar apenas mais um coeficiente dominante positivo seria insuficiente, pois ele pode cancelar com o bulk. As fórmulas de todas as portas permitem formular esse teste para direções polinomiais arbitrárias; passar de entradas finitas para uma lei uniforme e positiva continua aberto.

FIM DO RELATÓRIO — INTERIOR_GREEN_CRITICAL
