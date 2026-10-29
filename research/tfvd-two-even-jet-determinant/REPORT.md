# Dois jets pares: determinante conjunto e quatro caixas da fonte TFVD

**PARTIAL.** O alvo da PR #66 recebeu uma identidade exata de cutoff na fonte C3 completada, com quatro slots e todos os termos mistos de cauda. O sinal da seção de dois jets foi reduzido a um polinômio em **quatro jets completos de F**, sem calcular uma série de `1/F`. Foi demonstrado no Lean que erro absoluto de até **10⁻¹²** em cada um desses quatro jets, em torno dos centros racionais abaixo, é suficiente para provar `h₀h₂−h₁²>0`.

**A inclusão da fonte verdadeira nas quatro caixas não foi provada. Não há novo sinal canônico incondicional nem positividade all-order.**

Base: `296ba5ed7c89eb610a9a7ccec7b5e57cc323e0b5`, HEAD da PR #66.
Branch: `agent/tfvd-two-even-jet-determinant`, empilhada sobre `agent/tfvd-joint-response-transport`, sem merge automático.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
Operador consultado em `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem alterações. Main, PRs anteriores, fontes, métricas, câmeras, amplitudes, fases, pins, worktrees e arquivos alheios foram preservados.

## A — O que já estava demonstrado

- A PR #66 fornece `CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient`, `physical_polarized_numerator`, `fullSources_eventually_jointKernel` e `critical_jointKernel_tendsto`: o numerador conjunto é da mesma fonte e seus coeficientes são os canônicos, com cruzamentos e completion.
- `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime` e `tfvdStateTracePair_canonical` identificam o traço do estado enriquecido original com `(F,-F')`, mantendo as duas caudas armazenadas.
- `completedNativeGreenResponse_oddCoefficient_fullConvolution` e `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` fornecem a recorrência verdadeira sem pressupor sinal.
- `completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel` fornece a reflexão nativa. `completedNativeOperatorCharacteristic_zero_ne_zero` é o não anulamento central anterior.
- A PR #41 separa ortogonalização algébrica de positividade. Sua segunda direção é o residual `h₂−h₁²/h₀`, quando o prefixo h₀ é não nulo. Não se recebe seu sinal.
- A somação por partes do interior e seu cancelamento com o complemento oculto já estão na PR #58: `polarized_summation_parts`, `native_cutoff_boundary_exact`, `reduced_return_tail_defect`. Não se conservou um interior positivo depois de apagar sua cópia no oculto.
- A PR #61 controla superiores de multiplicadores e caudas na rota base dois. Essas cotas não são intervalos estreitos dos valores e não foram transportadas silenciosamente a um cutoff C3.

O trabalho novo concentra-se no retorno global C3 e na seção de dois jets pares. Profundidade vertical, endereço material, ordem de derivada e cutoff continuam distintos.

## B — O que foi demonstrado agora

Os nomes novos pertencem a `CarryTwoEvenJets`.

### Determinante sem inversão de uma cabeça

Escreva os coeficientes fatoriais da característica original:

$$f_{2j}=F^{(2j)}(0)/(2j)!,\qquad v=(f_0,f_2,f_4,f_6).$$

`native_three_convolutions` reaproveita a recorrência verdadeira:

$$h_0f_0=-f_2,\quad h_1f_0+h_0f_2=-2f_4,\quad
h_2f_0+h_1f_2+h_0f_4=-3f_6.$$

`native_two_even_determinant_clear` prova, sem dividir por prefixo ou cabeça,

$$\boxed{f_0^4(h_0h_2-h_1^2)=\mathcal D(v),}$$

$$\mathcal D(v)=v_0v_1^2v_2+3v_0^2v_1v_3-4v_0^2v_2^2.$$

`native_center_real`, `native_center_re_ne_zero` e `native_center_fourth_pos` demonstram, pela reflexão e não anulação originais, que f₀ é real e f₀⁴>0. **Essa positividade pertence apenas ao prefator.** `native_real_determinant` transporta a identidade à leitura real.

`response_two_even_determinant` liga a expressão à normalização da #66: para os coeficientes b de `a=-F'/F`, vale `b₁b₅−b₃²=4(h₀h₂−h₁²)`.

A simplificação operacional é efetiva: para esta seção, basta certificar quatro coeficientes de F, que dependem linearmente da sua síntese, e avaliar um polinômio racional. Não são necessários jets de `1/F`. A necessidade de certificar os valores de entrada permanece.

### Os dois traços completos e as caudas

`tracePiece` escreve a projeção linear original do par ordinário/logarítmico, conservando Xi e chart Q. `headTrace` e `tailTrace` leem campos do mesmo `CanonicalC3BracketTfvdCompletionState`.

`completedTrace_head_tail` prova, na seção física,

$$(F(z),-F'(z))=\mathrm{headTrace}_M(z)+\mathrm{tailTrace}_M(z).$$

O Green port armazenado não é substituído por esse readout nem declarado recuperável a partir dele. Não há novo carrier, métrica ou fonte. Os dois traços são sintetizados antes da observação dos jets.

`head_value_seed_cells` e `head_value_succ` identificam a cabeça com o prefixo literal:

$$F^H_M(z)=A(z)+\sum_{m<M}A(z)\,\mathrm{realCpSaturatedBracket}(3,m,s(z)),
\qquad A(z)=\Xi(z)/Q(s(z)).$$

Há uma única ocorrência da semente e dos fatores originais. `completedCell` conserva a célula centro–duas pernas inteira, sem somar módulos de pernas isoladas.

As regularidades de `head_value_analytic`, `completedCell_analytic` e `tail_value_analytic` são demonstradas. A cauda é a original; sua regularidade usa a identidade completa e a regularidade da fonte, sem pressupor uma troca de limite/derivada ponto a ponto.

`full_even_jets_head_tail` fornece `v=H_M+T_M`. `odd_jets_head_tail_cancel` prova separadamente

$$\mathrm{Jet}_{2r+1}F^H_M+\mathrm{Jet}_{2r+1}F^T_M=0.$$

Isso não permite declarar cada cabeça par. Cabeça e cauda são comparadores retidos no ledger, não fontes canônicas independentes.

### Regra discreta conjunta e todos os cruzamentos

Defina a forma de quatro slots independentes

$$\mathcal Q(a,b,c,d)=a_0b_1c_1d_2+3a_0b_0c_1d_3-4a_0b_0c_2d_2.$$

Ela é uma polarização algébrica, não um produto interno positivo. `polarizedQuartic_add_four` expande exatamente os 16 setores de cabeça/cauda.

`quartic_add_flux` demonstra `D(H+T)=D(H)+V(H,T)`, com

$$\begin{aligned}
\mathcal V(H,T)={}&\mathcal Q(T,H+T,H+T,H+T)\\
&+\mathcal Q(H,T,H+T,H+T)\\
&+\mathcal Q(H,H,T,H+T)+\mathcal Q(H,H,H,T).
\end{aligned}$$

Expandir os slots ainda recombinados recupera todos os 15 setores que contêm cauda, sem duplicação ou descarte.

Para os jets C_m das células originais, `head_even_jets_succ` prova `H_(m+1)=H_m+C_m`. A soma da regra discreta ao longo do cutoff produz `native_two_even_tfvd_ledger`:

$$\boxed{f_0^4(h_0h_2-h_1^2)
=\mathcal D(H_0)+\sum_{m<M}\mathcal V(H_m,C_m)+\mathcal V(H_M,T_M).}$$

É o teorema fundamental finito dessa sequência de prefixos, não uma isometria nem uma identificação de eixos geométricos. `determinantTail_step` prova a compensação entre o próximo incremento e o resto. `native_real_tfvd_ledger` aplica a leitura real somente depois de montar a soma.

Essa contabilidade não atribui o sinal de um somando ao total. `native_two_even_residual` e `native_two_even_critical_residual` conservam os coeficientes da segunda direção da #41; a divisão crítica exige apenas h₀≠0.

### Certificado racional de precisão suficiente

`quartic_unit_error` prova, para vetores complexos u,v de coordenadas com norma ≤1 e erro por coordenada ≤e,

$$\boxed{|\mathcal D(u)-\mathcal D(v)|\le32e.}$$

As quatro substituições ordenadas da mesma expressão são mantidas; não se aproximam separadamente energias divergentes.

Os centros exatos de `reference`, todos racionais de denominador 10¹⁵, são:

| Coeficiente completo | Centro decimal finito |
|---|---:|
| f₀ | `0.497120778188314` |
| f₂ | `−0.011485972157573` |
| f₄ | `0.000123452018070` |
| f₆ | `−0.000000832355481` |

Foram obtidos avaliando a característica C3 original com Xi/chart e cauda aproximada, sem momentos, theta, zeros ou alturas como entradas. São dados de testemunho, não redefinições da fonte.

`reference_norm` e `reference_quartic_lower` provam por cálculo racional no kernel

$$|q_j|\le1/2,\qquad \mathcal D(q)>10^{-10}.$$

`four_jet_error_suffices` demonstra

$$[\forall j,\ |v_j-q_j|\le10^{-12}]
\quad\Longrightarrow\quad \operatorname{Re}\mathcal D(v)>5\times10^{-11}>0.$$

O limite |v_j|≤1 é derivado das caixas. O orçamento é o erro conjunto `32×10⁻¹²`. `canonical_two_even_det_pos_of_four_jet_boxes` aplica esse certificado aos quatro coeficientes verdadeiros e obtém, **condicionalmente**, `h₀h₂−h₁²>0`.

A hipótese pendente é a inclusão nas quatro caixas. Não se recebe `PosDef`, contratividade ou o sinal desejado. A suficiência de precisão está provada; a realização dessas caixas pela fonte não está.

## C — O que foi refutado ou delimitado

A busca de incrementos nativos de sinal uniforme não recebeu suporte numérico:

- Em M=0, o polinômio da cabeça é aproximadamente `−6.68979×10⁻⁷`.
- Em M=1, o incremento é aproximadamente `−5.08962×10⁻⁵`.
- Em M=2, o incremento é aproximadamente `+1.25439×10⁻⁵`.
- Em M=32, o incremento volta a ser negativo: aproximadamente `−2.10178×10⁻⁷`.
- Em M=8, cabeça e resto conjunto são da ordem de 10⁻⁵; o valor recombinado observado é aproximadamente `1.19051334×10⁻¹⁰`.

São diagnósticos numéricos, não um no-go Lean da monotonicidade nativa. O polinômio da cabeça não deve ser chamado de determinante canônico dessa cabeça, que tem jets ímpares não nulos. A identidade formal registra a recombinação necessária antes dessa interpretação.

A regressão Lean contém um controle algébrico auxiliar: uma cauda pode ter polinômio próprio zero e contribuição mista não nula. Isso impede sua omissão automática, sem afirmar que o exemplo seja uma fonte C3.

Não foi refutada a positividade canônica. O controle auxiliar da #66 mantém seu alcance: composição, paridade e diagonais radiais positivas não bastam para todos os cruzamentos.

## D — Kernel, validação e limites

Os seis módulos matemáticos são `TwoJetInvariant`, `CompletedTraceJets`, `QuarticFlux`, `RealLedger`, `QuarticError` e `FourJetWitness`. São **40 teoremas e 16 definições**, em **56 raízes públicas**. `Audit.lean` imprime os axiomas e percorre tipos e corpos transitivamente, permitindo apenas `propext`, `Classical.choice`, `Quot.sound` e bloqueando consumidores posteriores de positividade indicados no guard.

**Validação final: 18/18 verificações passaram**, incluindo os oito módulos de pesquisa, os builds focado e raiz com `--wfail`, as três auditorias e a regressão das doze fontes. Os fechamentos transitivos por grupo visitaram 5.251, 5.234, 5.259, 5.257, 1.412 e 5.142 constantes; só os três axiomas fundacionais permitidos foram encontrados. Os fechamentos têm sobreposição e não devem ser somados como constantes distintas. Não há placeholders, novos axiomas matemáticos, `sorry`, `admit` ou `native_decide`.

`experiment.py` reutiliza somente as funções C3 da #65, sem efeitos de topo. Dois prefixos J=64,128 usam sete jets fatoriais, 70 casas e a aproximação Taylor/EM documentada. Não se força a anulação dos jets ímpares: os resíduos de ordem 10⁻³⁵ e 10⁻⁴⁰ estão registrados. O erro observado contra os centros racionais é menor que 10⁻¹² nas duas avaliações; isso não é um intervalo certificado da fonte.

A expansão de quatro slots e o resto também são testados com `Fraction`. O polinômio racional é aproximadamente `1.19051331×10⁻¹⁰`; o valor completo observado é `1.190513342793716…×10⁻¹⁰`. Os números são regressões; as afirmações de sinal certificadas são as condicionais acima.

Reprodução no host preparado:

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/tfvd-two-even-jet-determinant
python3 research/tfvd-two-even-jet-determinant/validate.py
```

O script compila os módulos com `warningAsError`, executa `lake build --wfail` focado e raiz, auditorias Foundation/Geometry/Analysis, regressão das doze fontes e preservação histórica. Os caches ancestrais estão explícitos em `compile_module.sh`; não se reivindica bootstrap de clone vazio sem esses módulos de pesquisa. Logs, comandos e hashes estão em `evidence/`.

## E — Próximo passo mínimo

A obrigação de avaliação passou a ser **quatro caixas dos coeficientes de F**, com erro absoluto 10⁻¹²:

$$\forall j\in\{0,1,2,3\},\quad
\left|F^{(2j)}(0)/(2j)!-q_j\right|\le10^{-12}.$$

Para descarregá-las pela mesma fonte: certificar os jets 0…6 dos fatores Gamma/Xi e chart originais, combiná-los linearmente com os jets do bracket C3 e suas caudas aceleradas, e usar as identidades de cabeça+cauda demonstradas. Não receber valores mpmath como intervalos. Não transportar cotas base dois a C3 por semelhança de stencil; qualquer reaproveitamento exige crosswalk com os endereços corretos.

O ledger conjunto já existe; outra telescopagem universal não selecionará seu sinal. Para all-order, permanece necessária uma propriedade independente que controle o resto conjunto na família nativa, preservando bordos e cruzamentos, além destas quatro caixas de uma seção finita.

**PARTIAL:** identidade conjunta e suficiência quantitativa racional demonstradas; caixas da fonte e causa de positividade all-order continuam abertas.
