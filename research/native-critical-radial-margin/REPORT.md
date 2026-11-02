# Margem radial crítica para oito fontes ímpares

**Classificação: PARTIAL para a origem geométrica do sinal; PASS para a comparação finita âncora–cauda na direção ímpar de oito fontes.** Trabalho baseado no commit ccd69cc7410c46ce9068d08852524df35cdc991f da PR #134, que permanece aberta. Nenhuma fonte, amplitude, métrica, perna, retorno ou coeficiente canônico foi modificado.

## A — O que já existia

A PR #134 prova, para a fonte completa e qualquer família finita fixa de jets ímpares, o orçamento absoluto dos incrementos $\sum |D_{K+j}-D_{K+j+1}|\le B(S,c)/(K+1)^2$. A PR #41 fornece a costura algébrica de Schur e a identificação da energia nativa de bordo com quatro vezes o pivô, sob invertibilidade do bloco anterior; nenhuma dessas identidades supõe o sinal do novo pivô.

O certificado integral material existente fornece caixas para os momentos canônicos originais por meio da fonte theta completa, com suas caudas. A positividade do quarto pivô ímpar já estava disponível por outro certificado finito. O objetivo aqui não é anunciá-la como uma descoberta nova, mas verificar a comparação da fonte física com a cauda da PR #134 e o transporte pela PR #41.

## B — O que foi demonstrado agora

Para o caso conhecido de seis fontes, [SixMargin.lean](SixMargin.lean) prova que o limite geral $B\le9\cdot10^7$ e a âncora integral preexistente implicam $D_K>B/(K+1)^2$, com $K=10^{20}-1$. SixBoundary.lean prova a passagem geral da margem finita ao limite e reobtém o sinal do residual de seis fontes. O balanço da PR #130 é $2D_K$; o fator dois foi mantido.

Para oito fontes, $S=\{0,1,2,3\}$ e os jets são $1,3,5,7$. [EightCritical.lean](EightCritical.lean) usa os momentos originais para construir, por Cramer, $c=(c_0,c_1,c_2,1)$. A caixa da fonte prova que o determinante do bloco anterior é positivo; eight_critical_old_rows verifica exatamente as três equações do bloco, sem usar um teorema de sinal do novo pivô.

As caixas certificadas em EightInputs.lean abrangem $h_1,\ldots,h_7$. [EightHead.lean](EightHead.lean) usa todas as 16 contribuições ordenadas e prova, por aritmética intervalar do kernel,

$$
\operatorname{oddCanonicalForm}(S,c)>10^{-23}.
$$

A estimativa obtida por um programa racional auxiliar é apenas diagnóstico; a desigualdade acima é a declaração Lean. Ela emprega a entrada integral theta já formalizada e, portanto, **já determina o sinal da forma canônica**. A identidade da PR #41 confirma que esta forma é o Schur procurado. Isso é uma demonstração finita proveniente das caixas, não uma causa geométrica independente do sinal.

[EightMargin.lean](EightMargin.lean) e [EightQuantitative.lean](EightQuantitative.lean) mantêm as 16 parcelas e provam, na normalização fullEnergy e em $K=10^{20}-1$,

$$
B(S,c)\le16\cdot10^9,\qquad
\frac{B(S,c)}{(K+1)^2}\le1{,}6\cdot10^{-30},
\qquad D_K>9\cdot10^{-24}.
$$

Logo $D_K>B(S,c)/(K+1)^2$. O corte explícito garantido pela PR #134 é 32 para esta família; a âncora escolhida é posterior. O índice K pertence à regularização radial e não é a profundidade vertical do Carry. O limite físico tem sinal positivo via finite_odd_boundary_positive_of_anchor.

[EightSchurCore.lean](EightSchurCore.lean) identifica o vetor de Cramer com $-A^{-1}b$ e a forma com sourceMomentSchur da sequência original, setor deslocado 1, índice 3. [EightSign.lean](EightSign.lean) aplica a cauda e [EightNative.lean](EightNative.lean) aplica a costura da PR #41 e transporta ao estado de bordo ímpar de oito fontes, com o fator quatro original.

## C — O que isso não demonstra

A margem não é uma lei universal e o experimento não extrapola a ordens maiores. Embora não tenhamos usado a positividade do pivô como hipótese ou como certificado anterior, eight_head_strict_lower prova primeiro uma desigualdade de momentos que, pela igualdade crítica, já é equivalente ao sinal do pivô. Portanto, passar dessa desigualdade à âncora e voltar pela cauda é um transporte quantitativo válido, mas não constitui uma explicação geométrica independente de por que o pivô é positivo. Não se deve apresentar o retorno pelo limite como descoberta de um sinal que ainda estivesse aberto após a certificação do próprio head.

O resultado é sobre uma direção crítica fixa. Ele não prova a positividade uniforme da forma inteira, uma margem uniforme em ordens arbitrárias ou a positividade all-order das Hankel.

## D — Validação e dependências

Os novos módulos Lean foram compilados com warningAsError; o build raiz foi executado com lake build --wfail e as auditorias Foundation, Geometry e Analysis foram executadas separadamente. [Audit.lean](Audit.lean) verifica os axiomas dos 46 teoremas e percorre transitivamente 59.495 dependências de quatro resultados de oito fontes. Exige a entrada integral theta, o orçamento da PR #134 e a costura da PR #41, e exclui os certificados anteriores de sinal do alvo listados no próprio auditor.

As 200 dependências históricas de pesquisa verificadas por hash foram reutilizadas no cache isolado; não se trata de reconstrução limpa de todas as dependências. Os objetos da PR #134 foram inicialmente comparados por hash com a validação anterior e os nove módulos necessários dessa PR foram recompilados na reprodução, assim como os módulos novos e as cinco dependências necessárias da PR #41. A PR #134 e o trabalho não rastreado do checkout principal permanecem intactos.

## E — Próxima obrigação mínima

Certificar diretamente, pela síntese física na âncora e sem recorrer antes a uma desigualdade equivalente ao sinal da forma canônica, $D_K>B(S,c)/(K+1)^2$ para uma direção crítica além dos casos já cobertos. Isso exigirá um controle com sinal do pareamento completo que preserve retorno, bordos, cruzamentos e cauda. Uma expansão positiva obtida apenas após impor ou provar o sinal do próprio Schur não é uma explicação estrutural all-order.


Para reproduzir no servidor, com as dependências e o cache histórico verificado da PR #134 disponíveis, execute `bash research/native-critical-radial-margin/validate.sh --focused`; `--full` acrescenta o build raiz e as três auditorias de camada. O script recompila explicitamente as dependências usadas das PRs #41 e #134 e os módulos novos. Os logs, hashes e pressupostos de cache são registrados em `evidence/`.
