# Reconstrução radial com bordo retido e cauda completa de seis fontes

**Classificação geral: PARTIAL.** A reconstrução polarizada com o dado de escala finita foi formalizada para qualquer ordem finita. No terceiro crítico ímpar, provamos estrito decréscimo eventual do balanço físico e somabilidade absoluta de sua cauda radial, com cotas bilaterais. Não foi encontrada uma desigualdade independente que prove o sinal canônico em toda ordem.

Base: PR #128, commit `489a06ec9d4c61a7cfb68bd2288e5e23c2682692`, branch `agent/native-material-variation-six`, conferida aberta, draft e sem merge. Nova branch: `agent/native-boundary-euler-reconstruction`. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Execução no host `llm`.

## A — O que já estava demonstrado

- A reconstrução TFVD com os dois dados de bordo já está encerrada. `docs/R2_TFVD_GREEN_VALVE_ROUTE.md` registra o capstone; ela não é refeita nesta pesquisa.
- A #41 separa ortogonalização algébrica e sinal. A direção crítica pode ser selecionada usando a inversibilidade do bloco antigo; isso não prova positividade do residual novo.
- `nativeSourceProjectiveBoundaryJetSynthesis` sintetiza todos os jets pares e ímpares antes do readout. `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto` conserva seus cruzamentos e fornece a expressão nativa de bordo em duas entradas complexas independentes.
- `originalBoundaryPair`, da #125, é uma abreviação transparente dessa expressão. `primeDepthGeometricMoment_eq_canonical` identifica os momentos dessa leitura com os canônicos, sem hipótese de positividade.
- A #128 demonstrou a variação material completa e a lei `hρ′−(m+n+1)ρ` para jets arbitrários. A camada de grau m+n+1 é anulada pelo filtro de variação. Isso não exclui sua recuperação pelo dado original de bordo.
- A mesma #128 demonstrou `six_exact_remainder`, `six_physical_energy`, `six_critical_correction_positive` e `six_original_correction_tendsto`. A correção positiva vem das inclusões integrais originais, não do sinal do pivô.

O índice k usado abaixo é a regularização radial, com hₖ=1/(k+1). Não é profundidade vertical Carry, ordem de jet, endereço material ou mudança de câmera. Nenhuma dessas coordenadas é identificada por analogia.

## B — O que foi demonstrado agora

### B.1 — Reconstrução com o dado de escala finita

[RadialReconstruction.lean](RadialReconstruction.lean), `radial_partial_sum`, prova para qualquer sequência num grupo normado:

$$\sum_{j=0}^{M-1}(f_{K+j}-f_{K+j+1})=f_K-f_{K+M}.$$

`radial_partial_sum_tendsto` conserva o dado fK quando f converge. A aplicação física, `complete_pair_boundary_reconstruction`, usa exatamente

$$B_k(x,y)=\mathcal B\big(\operatorname{nativeSourceProjectiveBoundaryJetSynthesis}(n,k,x),\operatorname{nativeSourceProjectiveBoundaryJetSynthesis}(n,k,y)\big).$$

Então, para todo n, K e duas entradas complexas independentes x,y,

$$\boxed{L_n(x,y)=\lim_{M\to\infty}\left[B_K(x,y)-\sum_{j=0}^{M-1}(B_{K+j}(x,y)-B_{K+j+1}(x,y))\right].}$$

L é o `originalBoundaryPair` preexistente, com as mesmas fases pares/ímpares e os mesmos momentos canônicos já identificados. Nenhum kernel substituto ou métrica nova é introduzido. A identidade conserva a síntese completa e os cruzamentos finitos antes do limite; não postula ortogonalidade entre setores em escala finita.

**Limite de alcance:** para entradas complexas arbitrárias, foi provada a convergência das somas parciais na ordem radial. Isso, sozinho, não autoriza afirmar somabilidade absoluta ou reordenar a série. `radial_drop_hasSum` acrescenta essa conclusão real quando os decrementos completos são não negativos; sua hipótese será demonstrada na fonte de seis endereços em B.3.

### B.2 — O resto analítico orienta passos adjacentes

[AnalyticRadialTail.lean](AnalyticRadialTail.lean) trabalha com a expansão completa

$$f(h)=L+Ch^2+h^3\operatorname{Re}R(h),\qquad R\text{ analítica no centro}.$$

`quadratic_extension_derivative` calcula

$$f'(h)=h\left(2C+3h\operatorname{Re}R(h)+h^2\operatorname{Re}R'(h)\right).$$

`quadratic_extension_strictMono` prova: se C>0, existe ε>0 tal que f é estritamente crescente em 0<h<ε. Não há hipótese de sinal sobre L. A continuidade de R e R′ controla o resto inteiro. Este passo seria inválido se usasse apenas f=L+Ch²+o(h²), sem regularidade suficiente do resto.

### B.3 — Aplicação à fonte original de seis endereços

[SixBoundaryReconstruction.lean](SixBoundaryReconstruction.lean) define `sixPhysical` somente como abreviação da diferença das normas dos **dois estados físicos originais**, para a família

$$X_k=\operatorname{jet}_5(k)+u_*\operatorname{jet}_3(k)+v_*\operatorname{jet}_1(k).$$

As amplitudes, fases, fatoriais e os seis endereços são os da #128. Os 36 cruzamentos e a cauda analítica da resposta original permanecem. `six_physical_analytic_extension` aplica o resto completo já provado e confere a igualdade na grade nativa.

Escrevendo Dₖ=`sixPhysical k`, L=`sixLimit sixU sixV`=2p₃ e C=`sixCorrection sixU sixV`, temos:

$$\boxed{D_{k+1}<D_k\quad\text{para todo k suficientemente grande}.}$$

Esse é `six_physical_eventually_decreasing`, resultado novo além de Dₖ>L eventualmente. C>0 é o certificado da fonte reaproveitado; não se usa o antigo sinal de p₃.

`six_boundary_tail` prova que existe N tal que, para cada K≥N, todos os decrementos ΔDₖ=Dₖ−Dₖ₊₁ são positivos e

$$\boxed{2p_3=D_K-\sum_{j=0}^{\infty}\Delta D_{K+j},\qquad \sum_{j=0}^{\infty}|\Delta D_{K+j}|<\infty.}$$

O `HasSum` e a somabilidade absoluta são demonstrados para essa fonte real; não inferidos da convergência polarizada geral de B.1. O termo de escala finita e a cauda são ambos preservados.

`six_accumulated_tail_scale` quantifica o tamanho da **cauda inteira**, sem descartá-la:

$$\frac C2 h_K^2<\sum_{j=0}^{\infty}\Delta D_{K+j}<\frac{3C}2 h_K^2\qquad(K\text{ suficientemente grande}).$$

Os fatores 1/2 e 3/2 são margens do limite já provado, não alterações de pesos ou da fonte. O índice N é existencial, não calculado. Os testes diagnósticos não fornecem o N da prova Lean.

### B.4 — Um orçamento suficiente, com obrigação explícita

[TailControls.lean](TailControls.lean), `boundary_error_of_increment_budget`, prova uma ferramenta quantitativa. Se fₖ→L, B≥0 e os incrementos **efetivos** satisfazem

$$|f_{K+j}-f_{K+j+1}|\le B(h_{K+j}^2-h_{K+j+1}^2)\quad\text{para todo j},$$

então |fK−L|≤BhK². `positive_boundary_of_increment_budget` conclui L>0 se, adicionalmente, fK>BhK².

Esse resultado não demonstra o orçamento para a fonte canônica em toda ordem. Ele separa duas avaliações concretas — o saldo na escala finita e a cauda acumulada — sem receber L>0 como hipótese. Não é anunciado como mecanismo geométrico de sinal já descoberto.

## C — O que foi refutado ou delimitado

Uma cauda positiva subtraída do saldo inicial dá uma **cota superior** para o termo constante. Não fornece a cota inferior procurada. Mesmo positividade estrita em toda escala finita e estrito decréscimo não garantem limite estritamente positivo.

`positive_decreasing_zero_boundary` formaliza o controle exato fₖ=hₖ²: todos os seus termos são positivos, todos os passos decrescem e o limite é zero. `increments_ignore_constant` prova que os decrementos não detectam uma constante aditiva.

Esses controles são sequências abstratas usadas para testar a inferência lógica. Não são fontes alternativas Carry, não alteram o estado original e não demonstram um NO-GO da geometria. Excluem somente a dedução de sinal estrito a partir das propriedades listadas isoladamente.

O script [mechanism_probe.py](mechanism_probe.py) executa 256 telescopagens complexas racionais exatas e 87 controles exatos de invariância por constante. Nos dados canônicos existentes, testa 370 decrementos e quatro reconstruções com cauda remanescente explícita. Os diagnósticos retêm os 36 cruzamentos do readout, mas usam um prefixo de momentos sem cota analítica de truncagem. São experimentos finitos; a prova de B.3 usa a fonte analítica completa.

## D — O que permanece aberto

Não foi demonstrado que o dado de escala finita domine toda a cauda em cada direção canônica, em toda ordem. A positividade de H6/K6, das doze fontes ou do pivô p₃ já conhecido não entra nas provas novas de sinal da correção e de monotonicidade.

Não há uniformidade em n, operador infinito, representação Gram canônica all-order ou transporte unitário para estados theta demonstrado aqui. Não se afirma convergência individual das duas pernas cujas normas podem divergir. A série de B.3 soma diferenças do balanço completo, não as energias divergentes separadamente.

O sinal de C no teste de seis endereços usa as caixas integrais históricas da própria sequência, com redução racional pelo kernel. A reconstrução polarizada geral e as identidades de soma não usam essas caixas. Nenhuma equivalência com Stieltjes ou PosDef foi usada como prova incondicional.

## E — Próximo passo mínimo e reprodução

O dado perdido pela derivada foi recuperado de modo explícito: saldo original de escala finita menos a cauda completa. A orientação positiva da cauda foi provada no teste de seis fontes e não resolve o sinal do que sobra.

O próximo teste deve obter **cotas efetivas provenientes da mesma fonte** para o saldo inicial e para os incrementos, em uma mesma escala, e verificar uma dominação estrita. Uma realização concreta é descarregar o orçamento de B.4 e provar fK>BhK² sem usar o sinal do residual. Antes de tentar uniformidade na ordem, testar essa estimativa no crítico ímpar já identificado, conservando o resto analítico completo. Apenas aumentar o número de coeficientes ou postular a mesma margem com outro nome não resolve essa obrigação.

Nenhuma desigualdade all-order independente para essa dominação foi encontrada nesta rodada. As novas identidades e o controle da cauda delimitam a tentativa; não transformam a lacuna em uma hipótese supostamente satisfeita.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

O cache opcional da #128 contém 186 objetos de provas anteriores, verificados contra fontes, objetos, toolchain, manifesto, pins e fontes nativas. SHA256 do arquivo de entrada: `abf4f5b1df9fe4b3fd12ce2099ebbce19150f4fb441226275b5f7977dfe200e6`. Ele deve estar em `.cache/input-cache.tar.gz`; sem esse cache, `python3 validate.py` recompila os ancestrais exatos. Os quatro módulos novos e a auditoria são compilados nesta execução.

Checkpoint diagnóstico: `momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv`, coluna `canonical_h`, SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`. Foram usados os 64 momentos existentes e 160 dígitos aritméticos, sem calcular novos momentos, alturas ou zeros.

### Validação concluída

**17 checks passaram**, todos com exit 0, incluindo as compilações individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. São **19 teoremas e 3 definições públicas**, em quatro módulos matemáticos novos. Os 186 objetos ancestrais foram verificados e reutilizados; não foram anunciados como recompilados. Passaram os 256 controles complexos racionais, os 87 controles de constante e os quatro diagnósticos com 370 decrementos.

As 22 raízes públicas têm `#print axioms` e auditoria transitiva de tipos e corpos opacos. Grupo algébrico: 14 raízes e 33705 dependências; fonte: 5 e 58459; certificação: 3 e 64095. A auditoria exige a presença efetiva do limite polarizado nativo e da expansão/identificação física completas no grupo da fonte; no grupo de certificação, exige também as inclusões integrais primitivas. Os consumidores enumerados de positividade canônica finita são proibidos. Só são permitidos `propext`, `Classical.choice`, `Quot.sound`.

Sem `sorry`, `admit`, `native_decide` ou novos axiomas. Fontes, pesos, métrica, amplitudes, completion, dressing, pins e trabalho anterior foram preservados. As evidências estão em `evidence/validation.json`, `evidence/kernel-audit-summary.json`, `evidence/upstream.json` e `evidence/preservation.json`; `SHA256SUMS` registra a integridade. Validação observada no host `llm`, sem alegação de CI externo.

Entrega em PR draft empilhada sobre a #128, sem merge automático. Fontes e cache são arquivados e verificados localmente antes da remoção apenas do worktree próprio. A branch publicada e todos os trabalhos anteriores são preservados.

Fim do relatório — bordo retido, cauda completa reconstruída e monotonicidade de seis fontes provada; dominação estrita e positividade canônica all-order permanecem abertas.
