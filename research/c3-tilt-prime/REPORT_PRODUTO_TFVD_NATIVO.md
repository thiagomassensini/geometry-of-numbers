# Produto literal TFVD e cruzamentos na direção crítica

**Resultado: PARTIAL.** Para cortes suficientemente grandes, a lei de produto de Bézout foi aplicada aos jets literais da cabeça e da cauda TFVD da fonte completada, nos dois setores, com dois argumentos independentes. A correção **total** em relação ao bloco da cabeça coincide exatamente com os três cruzamentos que contêm cauda e é limitada por um orçamento já provado que tende a zero para cada ordem e direção fixas. Não se demonstra o sinal all-order dos pivôs, margem uniforme em ordem ou sinal das parcelas separadas.

## Proveniência e objetos

Base `9ed8fa16d23de78bbe48fdad51697e98ef0d2844`, PR #146 empilhada na #145, branch `agent/c3-critical-tilt-prime`. O estado completo é a fonte TFVD original e suas portas: `NativeTrace.completedTrace_head_tail` decompõe o par completado `(F,−F′)` em cabeça e cauda **antes** da projeção para os jets. `literalHead M n` e `literalTail M n` são os jets pares de altura da primeira componente desses traços, incluindo completion, chart e cauda originais. `literal_head_tail` prova `nativeC = literalHead M + literalTail M` depois da extração; essa é a mesma sequência `nativeC` que alimenta a congruência com os momentos canônicos.

Escrevemos `H_M` e `T_M` para as séries formais nesses jets, e `C` para a série canônica completada. Cabeça e cauda físicas não são pressupostas pares em altura: `H_M` e `T_M` são suas **subsequências pares**, e não se afirma que `H_M(z²)` reconstrua os traços completos. O produto e o quociente abaixo são operações sobre seus coeficientes formais, após a síntese completa; não definem um novo estado físico nem afirmam que um quociente de estados ou de funções físicas tenha sido construído.

## Resultados novos em Lean

1. `literal_head_constant_eventually_ne` prova, sem hipótese sobre o novo pivô, que o coeficiente constante da cabeça é não nulo para `M` suficientemente grande. A prova usa `literal_head_tendsto 0`, a cota da cauda já certificada e a não anulação original de `nativeC 0`. Não é fornecido um valor numérico de `M`.
2. Define-se a correção formal exata `D_M=1+H_M⁻¹ T_M`. Para cada `M` com cabeça invertível, `literal_product_series` e `literal_product_coefficients` provam `C=H_M D_M` coeficiente a coeficiente. `literalCorrection_constant_ne` prova que o termo constante de `D_M` também é não nulo. `literalCorrection_zero_tendsto_one` prova somente `(D_M)_0→1`, sem afirmar aqui convergência de todos os demais coeficientes ou de funções analíticas.
3. `literal_product_blocks` especializa a regra de produto demonstrada anteriormente aos fatores literais `H_M,D_M`, em todo tamanho e ambos os setores. `literal_product_pair` transporta a identidade para `x,y` reais independentes, depois complexificados, conservando o pareamento **bilinear** existente. Não se afirma que este seja o produto interno sesquilinear da Gram física de Green.
4. `literal_product_critical` toma ambos os argumentos como `monicSourceDirection nativeC nativeH ...`, a direção da ortogonalização algébrica da PR #41. Ele identifica a soma completa das duas parcelas do produto com `nativeC 0 * nativeSourceSchurRemainder ...`. Sua hipótese `IsUnit` é a invertibilidade do prefixo de momentos anterior; o sinal do novo pivô não é hipótese nem conclusão.
5. Escreva `P_M(x,y)` para a soma dos dois blocos transportados do produto e `HH_M(x,y)` para o pareamento cabeça–cabeça da decomposição literal original. `literal_product_difference_eq_mixed` prova exatamente

   \[
   P_M-HH_M=HT_M+TH_M+TT_M.
   \]

   À esquerda, **ambas** as parcelas do produto e a diferença entre a cabeça transportada e a cabeça original fazem parte da correção total. Não se identifica o bloco de `D_M` isoladamente com `HT+TH+TT`. O lado direito mantém os três cruzamentos ordenados originais.
6. `literal_product_difference_bound` reutiliza `literal_error_bound` para demonstrar, para dois argumentos independentes,

   \[
   \|P_M(x,y)-HH_M(x,y)\|\leq E_M(x,y),
   \quad E_M=E_{HT}+E_{TH}+E_{TT}.
   \]

   `literal_product_difference_tendsto_zero` combina essa desigualdade com `literal_error_budget_tendsto_zero`: `E_M→0`, e portanto a correção **total** tende a zero, em cada setor, dimensão e par de direções fixos. O valor de `M` no qual a cabeça é não nula é eventual, não efetivo neste resultado.

## O que não decorre

A norma da correção tendendo a zero não demonstra que `HH_M` possua uma margem positiva nem que `P_M` ou o pivô sejam positivos. A cota é absoluta, para dimensão e direções fixas; não está demonstrada uniformidade em ordem, setor ou direção crítica variável. Tampouco foram provados separadamente o sinal ou a convergência do bloco de correção do produto. O resultado é uma identidade de readout e coeficientes; não iguala Gram física Green, kernel de Bézout e Hankel, nem constrói equivalência unitária entre carriers.

## Validação

Módulos novos: `NativeProductFactor.lean`, `NativeProductTransport.lean` e `NativeProductTransportAudit.lean`. A compilação individual usa avisos como erros. Os `#print axioms` das novas raízes mostram apenas `propext`, `Classical.choice`, `Quot.sound`. A auditoria transitiva verifica raízes e rejeita consumidores de caixas theta e sinal nomeados; não substitui uma auditoria semântica de todas as equivalências possíveis.

```bash
bash research/c3-tilt-prime/validate_native_product.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

As saídas estão em `research/c3-tilt-prime/evidence/`. As dependências anteriores são reutilizadas por seus caches; não se reivindica reconstrução limpa dos repositórios externos. Os repositórios e arquivos históricos não foram alterados.

## Próxima obrigação mínima

Na mesma direção crítica de cada setor e ordem, obter uma **margem para a parte principal literal que domine explicitamente o orçamento completo das três parcelas de cauda**, por argumentos da fonte anteriores ao sinal do novo pivô. Primeiro testar se existe uma cota relativa com dependência explícita de ordem e cutoff. A convergência absoluta por si só não fornece essa margem e, se for usada em sentido inverso a partir de um pivô positivo já conhecido, a aplicação vira circular.
