# Variação material completada, lei Euler dos jets e teste de seis endereços

Classificação: **PASS_STRUCTURAL para a fórmula material e o transporte em toda ordem finita; PARTIAL para a lei de sinal canônica all-order.** A orientação da primeira correção foi certificada na direção crítica ímpar de seis endereços, sem hipótese sobre o sinal do pivô novo.

Base: PR #127, commit `914bb03ba4d05a577b3c57406821be637af119bb`, branch `agent/native-moving-radial-balance`. Nova branch: `agent/native-material-variation-six`. A #127 foi conferida aberta, draft e sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Execução no host `llm`.

## A — O que já estava demonstrado

- A #127 identifica `curveState` com `physicalCompletedFiniteSource` na grade nativa, em qualquer dimensão finita, incluindo escala radial, amplitude projetiva e ambas as pernas. Seu `curve_euler_newton` conserva o diagrama físico Euler/Newton das #124–#125.
- A mesma PR demonstra o cancelamento polarizado da amplitude original e a derivada completa em coeficientes incidentes: dois termos de movimento mais a variação do retorno. Não é lícito manter a amplitude fixa implicitamente.
- O readout completado, depois da síntese, é

$$E_{x,y}(h)=\frac2h P_{\rho(h)}(x(h),y(h)),\qquad
P_r(x,y)=\sum_{i,j<N}\overline{x_i}y_j\frac{r_i+r_j}{i+j+2}.$$

Aqui ρᵢ(h) é o `responseReadout` original em (i+1)h; sua realidade provém da reflexão nativa, não de uma medida positiva postulada. Q=−F′/F da característica completada satisfaz Q(i(i+1)h)=2iρᵢ(h).

- `radialJetCoefficients`, `rawStencil` e `radial_jet_original_source` já fornecem os jets binomiais com seus fatoriais e a fase imaginária original. `projectiveChiralDifferenceJet` conserva as duas pernas.
- As inclusões `material_theta_integral_input` e `mem_logMomentBox` certificam os momentos originais. Seus consumidores posteriores de positividade finita não são premissas aqui.
- A distinção da #41 continua necessária: selecionar a direção crítica por um bloco antigo invertível não demonstra o sinal do residual novo.

O parâmetro h=1/(k+1) é a regularização radial existente. Não é a profundidade vertical Carry ou uma troca de câmera. Fora da grade, a curva usa a fórmula contínua do mesmo transformador; a derivada não é uma operação diferencial sobre uma sequência em ℕ.

## B — O que foi demonstrado agora

### B.1 — Fórmula material fechada, em duas entradas independentes

[MaterialVariation.lean](MaterialVariation.lean), teorema `scaled_material_hasDerivAt`, deriva exatamente:

$$\boxed{E'_{x,y}(h)=\frac2h\big(P_\rho(x',y)+P_\rho(x,y')\big)
+\frac2{h^2}P_{h\rho'-\rho}(x,y).}$$

Nenhum termo de amplitude, escala ou movimento foi descartado. Eles foram recompostos pelo cancelamento da fonte completada já provado na #127. [PhysicalMaterialVariation.lean](PhysicalMaterialVariation.lean), `physical_material_derivative`, transporta essa fórmula à forma complexa dos **dois estados físicos completos**, em toda dimensão finita N, com h>0, inputs diferenciáveis e regularidade da fonte.

`source_regular_local` prova a persistência local das condições de domínio e não anulação. `rho_differentiable` demonstra a regularidade do readout a partir da própria característica. Não se recebe um gate de sinal como hipótese de funcionamento.

### B.2 — Lei de escala dos jets em qualquer ordem

[JetEulerVariation.lean](JetEulerVariation.lean) conserva o input literal

$$X_{m,i}(h)=\frac{\mathrm{completedGreenForwardWeight}(m,i)}{m!(ih)^m}.$$

`radial_jet_vector_at_grid` confere seus coeficientes com `radialJetCoefficients`. `radial_jet_curve_original` e `radial_jet_curve_complete_jet` provam igualdade dos estados completos, desde que N>m; portanto não se omite o suporte original. Para um pareamento m,n completo, escolher N>max(m,n).

`radial_jet_hasDerivAt` demonstra, para todo m e h≠0,

$$hX'_m(h)=-mX_m(h).$$

Substituindo os dois movimentos na fórmula material, `physical_jet_material_derivative` obtém:

$$\boxed{E'_{m,n}(h)=\frac2{h^2}P_{h\rho'-(m+n+1)\rho}(X_m,X_n).}$$

O fator m+n+1 é derivado: m e n vêm dos dois inputs, e 1 da escala radial do pareamento. Não é um postulado de Hankel nem o clock material de frequências log(n+1). A métrica Cauchy e os endereços permanecem os originais.

### B.3 — Uma camada é anulada exatamente

`jet_kernel_monomial` calcula a ação sobre cada camada de Taylor de grau d:

$$\big(h\partial_h-(m+n+1)\big)(a h^d)
=(d-m-n-1)a h^d.$$

`canonical_layer_annihilated` formaliza o caso d=m+n+1: o resultado é zero. Trata-se de uma identidade sobre uma camada da expansão da fonte; a fonte inteira não foi substituída por um monômio.

Nos setores de mesma paridade, essa é precisamente a camada que produz o termo canônico constante do pareamento de jets, identificado pelas provas de limite anteriores. A identidade nova não determina o sinal dessa constante. A fonte completa a determina, mas o filtro de variação sozinho a elimina.

### B.4 — Mesma família original em seis endereços

[SixSource.lean](SixSource.lean) começa com parâmetros livres u,v, antes da escolha por momentos:

$$x_k(u,v)=\mathrm{radialJetCoefficients}(k,5)
+u\,\mathrm{radialJetCoefficients}(k,3)
+v\,\mathrm{radialJetCoefficients}(k,1).$$

`six_input_support` deriva seu suporte em {0,…,5}; isso é suporte do input, não corte da cauda analítica de F. `six_raw_at_grid` confere exatamente

$$x(h)=\frac{-i}{120h^5}\big(\Delta_5-20uh^2\Delta_3+120vh^4\Delta_1\big),$$

com os mesmos stencils assinados, fases e fatoriais. `six_curve_eq_original` identifica os dois vetores físicos. `six_closed_material_derivative` descarrega a regularidade da fonte e do input para esta família e aplica a fórmula B.1.

### B.5 — Expansão completa e seleção crítica

[SixTaylor.lean](SixTaylor.lean) soma os **36 cruzamentos** antes de reduzir às seis avaliações da resposta. `six_exact_remainder` usa a expansão analítica original com resto de ordem 14, não uma truncagem numérica. [SixEnergyTransport.lean](SixEnergyTransport.lean), `six_physical_energy`, identifica o readout resultante com Dₖ=||Iₖ||²−||Rₖ||² da mesma fonte.

Para parâmetros livres u,v, o limite é

$$L(u,v)=2\big(h_5+2uh_4+(u^2+2v)h_3+2uvh_2+v^2h_1\big),$$

e a primeira correção é

$$\boxed{C_6(u,v)=-10v^2h_2-168uvh_3-60(u^2+14v)h_4-484uh_5-182h_6.}$$

O resto completo dá Dₖ=L+C₆hₖ²+hₖ³ Re R(hₖ), com R analítica no centro. `six_original_correction_tendsto` formaliza diretamente o limite físico da diferença normalizada.

Só depois da construção da fonte selecionamos a direção crítica:

$$\delta=h_1h_3-h_2^2,\qquad
u_*=(h_2h_3-h_1h_4)/\delta,\qquad
v_*=(h_2h_4-h_3^2)/\delta.$$

[SixSign.lean](SixSign.lean) certifica δ>0 pelas caixas da fonte. `six_critical_old_rows` verifica as duas equações h₁v*+h₂u*+h₃=0 e h₂v*+h₃u*+h₄=0. O bloco antigo é resolvido algebricamente; não se supõe sinal do pivô novo.

`six_critical_limit_residual` reduz o limite a

$$L(u_*,v_*)=2(h_5+u_*h_4+v_*h_3)=2p_3,$$

o residual crítico do terceiro pivô ímpar. `six_critical_correction_positive` prova das mesmas inclusões racionais que C₆(u*,v*)>0. `six_original_eventually_above` transporta o sinal ao balanço físico:

$$\boxed{D_k>2p_3\quad\text{eventualmente}.}$$

Diagnóstico do checkpoint: u*≈−0,00618273203546; v*≈6,14315674688×10⁻⁶; 2p₃≈1,61635519233×10⁻¹⁶; C₆≈1,33490002917×10⁻¹⁴. Os decimais não são premissas Lean. O sinal certificado é o da correção; não foi usado o antigo certificado de positividade de p₃.

## C — O que foi refutado ou delimitado

- Retorno, amplitude e input não podem ser diferenciados como se só q variasse. A fórmula material conserva o conjunto e a lei dos jets mostra seu peso exato.
- A orientação positiva observada em quatro e seis endereços ímpares não prova uma orientação universal. Também não determina o sinal do limite.
- A identidade de anulação mostra exatamente por que o filtro de variação perde a camada constante relevante. Não é um NO-GO da geometria completa nem da recuperação do termo por dados de bordo já presentes na fonte.
- Não se apresentou uma Gram positiva auxiliar como a Hankel canônica. Não foram alterados a fonte, a amplitude, a métrica, as fases, o completamento ou os momentos.

O script [mechanism_probe.py](mechanism_probe.py) compara 18 polinômios completos dos canais com o readout, verifica 54 derivadas gaussianas racionais em entradas complexas independentes, 72 casos exatos da variação de jets e 1008 contribuições dos filtros de seis endereços. Os quatro diagnósticos canônicos calculam as duas energias e seu balanço com o checkpoint existente; não têm cota de truncagem e não substituem as provas analíticas.

## D — O que permanece aberto

A fórmula de variação e a lei m+n+1 valem para todas as ordens finitas sob suas condições de regularidade e suporte. A desigualdade C₆>0 é somente o teste de seis endereços. Não há prova de positividade canônica all-order, uniformidade na dimensão ou limite de operadores infinitos.

O termo p₃ é o limite constante, não sua primeira correção. A prova nova não presume nem demonstra de novo o sinal desse pivô já conhecido. Os certificados H6/K6 e das doze fontes permanecem preservados e não entram nas provas novas.

Não se afirma monotonicidade de Dₖ ou convergência separada das duas pernas. A derivada usa a extensão da fórmula nativa em h; a identificação com os objetos originalmente indexados por k foi provada na grade. Não se aplicou um operador não limitado fora de seu domínio.

## E — Próxima obrigação mínima e reprodução

O alvo da #127 foi fechado: a variação está escrita em coordenadas materiais e o teste de seis endereços foi transportado à fonte física original. A identidade em toda ordem localiza uma limitação: aumentar a ordem dos cálculos da variação não recupera automaticamente a camada que o próprio filtro anula.

O próximo ataque ao sinal precisa preservar e controlar o termo de bordo/constante da reconstrução original. Não basta provar mais uma orientação de Cₙ ou reobter a reconstrução TFVD, que já existe. É necessário encontrar uma desigualdade independente no saldo original de bordo, com os cruzamentos e o retorno, que forneça um limite inferior para o residual sem recebê-lo positivo como hipótese.

Nesta execução não foi encontrada essa desigualdade. A obrigação global continua sendo controlar a leitura canônica conservada; B.3 mostra por que a identidade diferencial isolada não a descarrega. Qualquer tentativa de integrar a fórmula B.2 precisa manter o dado de bordo que fixa essa constante, em dois argumentos independentes. Uma equivalência com Stieltjes ou PosDef não é sua demonstração.

Reprodução no host `llm`, na pasta desta pesquisa:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

O cache opcional da #127 contém 179 objetos, verificados contra fontes, hashes, toolchain, manifesto, operador e pins. SHA256: `03532447614a361758dac346adacfcf73a90e8dbc8ad364474cd7d16ff838e82`. Deve estar em `.cache/input-cache.tar.gz`. Sem ele, `python3 validate.py` recompila os ancestrais exatos. Não foi feita nova campanha de momentos ou quadratura.

Checkpoint diagnóstico: `momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv`, coluna `canonical_h`, SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`. Os diagnósticos usam 160 dígitos aritméticos dos dados existentes e não participam das provas Lean.

### Validação concluída

**20 checks passaram**, todos com exit 0. São **41 teoremas e 24 definições públicas**, em sete módulos matemáticos novos, além do módulo Audit gerado. As compilações individuais usam warnings como erros. Passaram os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis.

Foram reutilizados e verificados os 179 objetos da #127, incluindo seus certificados integrais antigos; nenhum foi anunciado como recompilado nesta execução. Passaram 18 comparações exatas dos canais completos, 54 controles exatos da derivada material, 72 controles exatos da lei dos jets, 1008 contribuições dos filtros de seis endereços e quatro diagnósticos canônicos.

As 65 raízes públicas possuem `#print axioms` e auditoria transitiva de tipos e corpos, incluindo opacos com `value? (allowOpaque := true)`. O grupo algébrico tem 24 raízes e 23508 dependências; o grupo da fonte, 26 e 57544; o grupo de certificação, 15 e 58591. Os certificados finitos de positividade canônica enumerados e as equivalências indicadas estão proibidos na auditoria. A certificação exige a presença efetiva das inclusões integrais, da identificação da energia física original e do resto analítico completo. Só são aceitos os axiomas fundacionais `propext`, `Classical.choice`, `Quot.sound`.

Não há `sorry`, `admit`, `native_decide` ou novos axiomas. Fontes, pesos, métricas, amplitudes, dressing, completion, pins e trabalhos antigos foram preservados. As evidências estão em `evidence/validation.json`, `evidence/kernel-audit-summary.json`, `evidence/upstream.json` e `evidence/preservation.json`; `SHA256SUMS` registra os arquivos da entrega. Validação observada no host `llm`, sem reivindicação de CI externo.

A publicação usa PR draft empilhada sobre a #127, sem merge automático. Fontes e cache verificados são arquivados localmente antes da remoção somente do worktree próprio; a branch e todos os trabalhos anteriores são preservados.

Fim do relatório — variação material e lei Euler em toda ordem formalizadas, seis endereços preservados e correção certificada; sinal canônico all-order permanece aberto.
