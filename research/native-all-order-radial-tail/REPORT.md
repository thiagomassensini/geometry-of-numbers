# Orçamento da resposta nativa em famílias finitas arbitrárias

**Classificação: PARTIAL.** A cota da resposta e o pareamento físico completo foram transportados para qualquer quantidade finita de endereços. Ainda não foi construído o orçamento dos incrementos radiais com jets móveis nem demonstrada uma lei geométrica de sinal all-order.

## A — O que já estava demonstrado

A base é `2ff2c743472463b20a99e1384d78be7c20840d5a`, cabeça da PR #130, sobre `agent/native-effective-radial-budget`. A #130 fornece `CarryEffectiveRadial.native_response_prefix_error`, uma cota explícita para a cauda completa da resposta logarítmica original em qualquer truncamento; `imaginary_radial_regular` garante os denominadores originais na faixa certificada. Ela também controla a derivada do resto e fecha um orçamento de incrementos e um saldo positivo para a família crítica específica de seis endereços. A cota de coeficientes reaproveitada tem proveniência analítica existente: não afirmamos que ela seja uma nova demonstração puramente geométrica.

`CarryMovingRadial.fullPair_eq_response` identifica, **depois da síntese completa**, o pareamento físico com amplitude e retorno originais à leitura polarizada da resposta. `CarryMaterialVariation.materialPair` conserva os dois argumentos independentes e todos os pares ordenados de endereços. A PR #41 separa a ortogonalização algébrica dos sinais dos pivôs; nenhum sinal de pivô é usado nesta extensão.

## B — O que foi demonstrado agora

Em [AllOrderTail.lean](AllOrderTail.lean), com `a=22/175`, defina o endereço original `z_i=i(i+1)h` — aqui o primeiro `i` é a unidade imaginária — e

$$\delta_{i,M}=|z_i|\,\frac{a(a|z_i|^2)^M}{1-a|z_i|^2},\qquad E_{N,M}=\sum_{i<N}\delta_{i,M}.$$

A hipótese de domínio explícita é `N |h| < 1/4`. `finite_grid_radius` e `finite_radial_regular` certificam o disco e a não anulação dos dois denominadores originais em cada um dos N endereços, também para N=0. `native_address_prefix_error` limita o erro entre a resposta original `rho` e sua truncagem `rhoPrefix` por `delta_{i,M}`.

`material_pair_uniform_error` demonstra, para dois vetores complexos independentes e qualquer N, que uma perturbação pontual limitada por ε produz erro no pareamento de no máximo

$$\varepsilon\left(\sum_{i<N}|x_i|\right)\left(\sum_{j<N}|y_j|\right).$$

A prova soma todos os cruzamentos `i,j`, mantendo o denominador original `i+j+2`. Em particular, não troca a métrica física por uma norma escolhida para fabricar positividade.

`native_finite_grid_budget` aplica essa desigualdade com `ε=E_{N,M}` à resposta original. `full_physical_grid_budget` a transporta para `CarryMovingRadial.fullPair`, incluindo o fator físico `2/h`, sob `h>0`. Assim a diferença entre o pareamento físico completo e sua expressão truncada é limitada por

$$\frac{2}{h}E_{N,M}\left(\sum_i|x_i|\right)\left(\sum_j|y_j|\right).$$

A soma dos erros por endereço é uma escolha conservadora e calculável; não é reivindicada como ótima. `address_budget_tendsto_zero` e `family_budget_tendsto_zero` provam que, **para N e h fixos**, o orçamento tende a zero quando M cresce. Os fatores `x`, `y` e `h` também precisam ser fixados para inferir convergência do erro físico a partir dessa cota. Não há aqui convergência uniforme quando N cresce ou quando h tende a zero.

## C — O que foi refutado ou delimitado

Nenhuma impossibilidade geral da geometria foi demonstrada. Uma cota absoluta não seleciona o sinal de um saldo: tanto um número positivo quanto um negativo podem ter módulo pequeno. Um prefixo positivo maior que o orçamento provaria positividade daquele caso, mas exigir tal desigualdade em todas as direções apenas deslocaria a obrigação se não vier de uma propriedade independente da fonte. A lei all-order solicitada ainda não foi encontrada.

As obstruções anteriores de margem relativa fixa e de coercividade uniforme permanecem relevantes. A cota presente não as supera por si. Tampouco mostra a existência de uma Gram canônica, de um operador infinito ou de uma identificação espectral. As cotas de fonte para `R'_M` da #130 ainda não foram transportadas aos jets móveis nesta investigação.

## D — O que permanece aberto

O próximo elo é obter, para uma família original dependente da profundidade, uma identidade diferenciável do pareamento completo com as derivadas de **ambos** os vetores, da resposta e do fator radial. É necessário limitar seu resto com constantes explícitas dependentes dos coeficientes e endereços, e integrar a cota entre pontos consecutivos da grade. A cota de valor aqui provada não controla automaticamente a derivada: duas funções próximas podem ter derivadas muito diferentes.

Mesmo esse orçamento de incrementos seria apenas controle de erro. Falta uma lei independente da síntese nativa que forneça, na mesma escala, um saldo crítico positivo maior que a cauda para cada ordem, preservando cruzamentos e bordos. Sem essa comparação não há conclusão de sinal; sem controle em N também não há passagem all-order uniforme.

## E — Próximo passo mínimo e reprodução

Provar uma versão para N arbitrário da identidade `materialVariation` aplicada à família original de jets móveis, conservar os três termos de derivada dos dois argumentos e da resposta, e combinar `source_remainder_deriv_bound` com limites explícitos das derivadas dos coeficientes físicos. Depois confrontar o saldo com essa cauda, buscando uma razão geométrica independente da positividade Hankel.

No host `llm`, com o checkout na base indicada e as dependências originais disponíveis:

```bash
python3 research/native-all-order-radial-tail/restore_verified_cache.py
bash research/native-all-order-radial-tail/validate.sh
```

A reprodução acima exige o arquivo `.cache/input-cache.tar.gz`, que contém os 200 objetos ancestrais da #130, SHA256 `d374041b5b017e2541039b6993ed3f53b244f20a1dd8c2e7bb851ba09eca288a`. O arquivo está disponível no pacote de evidências entregue junto com esta investigação. O restaurador verifica fontes, hashes e dependências antes de reutilizar qualquer objeto. A compilação nova e a auditoria de axiomas não são substituídas pelo cache. Evidências em `evidence/`; a validação não é uma afirmação de CI externo.

Fim do relatório — orçamento absoluto da resposta completa para qualquer família finita; orçamento de incrementos e lei de sinal all-order permanecem abertos.
