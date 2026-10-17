# Pivôs da fonte como balanço físico de incidente e retorno

## Resultado

A composição proposta no estudo anterior foi formalizada: para as duas paridades e em qualquer ordem fixa, o próximo pivô de Schur é metade do limite do balanço físico incidente menos retorno. A prova assume somente positividade do prefixo antigo; não assume contratividade do retorno nem o sinal do novo pivô.

A mesma construção conserva o pareamento complexo. Os termos cruzados entre os setores par e ímpar permanecem na regularização finita e convergem a zero pelo limite polarizado existente.

Além dos quatro testes de cada paridade já cobertos pela fonte de oito jets, foi obtida margem positiva para o quinto teste par. Ela usa o certificado integral infinito do PR #23. Isso controla uma direção concreta no retorno de dez fontes, sem certificar a contratividade desse retorno inteiro.

O quinto teste ímpar foi reduzido a uma desigualdade explícita sobre a fonte theta completa. Seu sinal permanece aberto. O certificado integral anterior cobre momentos theta até ordem 18; o novo alvo envolve também ordem 20.

## Proveniência e limites dos índices

Base: `geometry-of-numbers`, main em `997d46291d3fb54d1a023d726890d4cc006acd2c`, após PR #26. O operador é consultado em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, sem modificá-lo. Os módulos C2 não rastreados desse checkout foram preservados.

Reutilizam-se, literalmente:

- `sourceMomentMatrix`, `sourceMomentCoupling`, `sourceMomentSchur`;
- `sourceMomentSchur_sewing` e `sourceMomentSchur_critical_direction`;
- `nativeSourceBoundaryFromParity` e as fases de paridade originais;
- `nativeSourceChiralJetInput`, definido pela grade, pelos fatoriais, pelas diferenças finitas e pelas amplitudes completadas originais;
- `radialIncidentVector`, `radialReturnTransfer`, `storage`;
- os dois canais Jordan, positivo e negativo, do defeito original;
- o controle de erro e o limite polarizado dos jets completos;
- o certificado integral da fonte infinita do PR #23 e a oitava fonte do PR #26.

Aqui k é a regularização radial; n é o tamanho do prefixo de momentos; s=0 ou s=1 escolhe o setor par ou ímpar. Esses índices não são o tempo material, profundidades ou câmeras. O carrier usado é o Cauchy chiral existente. Não se afirma uma nova identificação com `baseTwoCompletedBoundaryHilbertState` ou uma nova equivalência global entre carriers.

Oito jets canônicos, de índices 0 a 7, separam-se em dois blocos de momentos 4 por 4. Não se trata de uma Hankel 8 por 8.

## 1. A direção crítica é aplicada à fonte existente

Defina

\[
A_{s,n}=(h_{i+j+s})_{i,j<n},\qquad b_{s,n}=(h_{i+n+s})_{i<n},
\]

\[
\sigma_{s,n}=h_{2n+s}-b_{s,n}^TA_{s,n}^{-1}b_{s,n},\qquad
v_{s,n}=(-A_{s,n}^{-1}b_{s,n},1).
\]

Os momentos apenas selecionam uma combinação de teste da família física previamente construída. Não se define um carrier a partir do Gram-alvo.

`parityCoordinates` insere essa combinação no setor apropriado usando a inversa das fases de paridade. O mapa é injetivo e a leitura de bordo satisfaz

\[
\mathcal B_{2(n+1)}(x_{s,n})=4\sigma_{s,n}.
\]

O fator quatro é o da torre Green original. A positividade do prefixo antigo é usada na identidade de Schur; o novo pivô pode ter qualquer sinal.

Declarações: `parityCoordinates_boundary`, `criticalCoordinates_boundary`, `parityCoordinates_injective`.

## 2. Transporte para os dois estados físicos

Aplicam-se as transformações existentes:

\[
c_k=\operatorname{nativeSourceChiralJetInput}(n+1,k,x_{s,n}),
\]

\[
X_k=\operatorname{radialIncidentVector}(k,2(n+1),c_k),\qquad
Y_k=\operatorname{radialReturnTransfer}(k,2(n+1))X_k.
\]

O balanço é o storage original:

\[
Q_{s,n}(k)=\|X_k\|^2-\|Y_k\|^2
=\operatorname{Re}\operatorname{storage}(k,c_k,1).
\]

Nenhum canal é apagado. Em particular,

\[
Q_{s,n}(k)=\|P^+_kX_k\|^2-\|P^-_kX_k\|^2.
\]

A presença de dois quadrados positivos não fornece, por si, o sinal da diferença.

Declarações: `criticalBalance_eq_storage`, `criticalBalance_eq_jordan`.

## 3. Limite exato e controle do erro

Para qualquer eta>0, eventualmente em k,

\[
|2Q_{s,n}(k)-4\sigma_{s,n}|\le\eta\|x_{s,n}\|^2.
\]

Consequentemente,

\[
\boxed{Q_{s,n}(k)\longrightarrow 2\sigma_{s,n}.}
\]

Ambas as identidades estão agora provadas em Lean, por `criticalBalance_eventually_error` e `criticalBalance_tendsto`.

Não se postulam derivadas globais adicionais, holomorfia de um estado de Hilbert ou contratividade. A regularidade e o controle usados são os já demonstrados para a síntese finita completa.

## 4. Polarização: os cruzamentos não desaparecem antes do limite

`criticalPairing` é o produto incidente menos o produto retornado, com duas direções independentes. A primeira entrada segue a convenção conjugada de Mathlib.

`criticalPairing_source` identifica esse produto com o balanço polarizado da fonte; `criticalPairing_eq_projective` o transporta à forma chiral original com o fator dois correto. `criticalPairing_conj` verifica a ordem dos argumentos e a conjugação.

`criticalPairing_self_tendsto` conserva ambas as quadraturas até o limite real. `criticalPairing_even_odd_tendsto` e `criticalPairing_odd_even_tendsto` demonstram separadamente os dois cruzamentos ordenados no limite. Não há enunciado de anulação desses cruzamentos em k finito.

## 5. A obrigação de margem ficou exata

Sob positividade do prefixo antigo,

\[
\sigma_{s,n}>0
\iff
\exists\varepsilon_{s,n}>0,\quad Q_{s,n}(k)\ge\varepsilon_{s,n}
\text{ eventualmente em }k.
\]

Essa é `criticalMargin_iff_pivot`. O teorema `criticalMargin_iff_jordanGap` conserva os dois canais e reescreve a obrigação como

\[
\|P^-_kX_k\|^2+\varepsilon_{s,n}\le\|P^+_kX_k\|^2.
\]

A margem pode depender de s,n. Não é preciso um único cutoff ou uma margem uniforme em toda ordem. Positividade em cada regularização, sem margem que sobreviva ao limite, não demonstra positividade estrita do pivô.

`AllCriticalMargins` recebe a margem como etapa de indução sobre o prefixo antigo positivo. `allCriticalMargins_matrices` executa a indução; `allCriticalMargins_iff_sourceRemainders` prova a equivalência com os dois restos originais da fonte em toda ordem. `allCriticalMargins_returnBounds` alimenta a torre física do PR #26, condicional a essa família de estimativas.

Isso identifica a obrigação analítica. Não é uma prova de sua validade em toda ordem.

## 6. Margem incondicional para o quinto teste par

O quarto bloco residual par do PR #23 é positivo a partir das integrais theta completas. `restoredEvenFiveFactor` reutiliza a restauração do canal central já existente. Sua identidade e seu determinante positivo demonstram

\[
(h_{i+j})_{0\le i,j<5}>0.
\]

Esse fator é apenas uma prova algébrica da forma da fonte, posterior à síntese. Não define novos vetores físicos nem substitui a porta de retorno.

Daí se seguem

\[
\sigma_{0,4}>0,\qquad
Q_{0,4}(k)\longrightarrow2\sigma_{0,4},\qquad
Q_{0,4}(k)>\sigma_{0,4}\text{ eventualmente}.
\]

Declarações: `even_source_five_posDef`, `fifth_even_pivot_pos`, `fifth_even_criticalMargin`, `fifth_even_sourceRemainder_pos`, `fifth_even_eventually_above_pivot`.

A dimensão da transformação física usada aqui é dez. O resultado certifica essa direção específica e seus dois canais completos. Não fornece norma do retorno de dez fontes menor ou igual a um.

## 7. Primeiro alvo ainda aberto: quinto teste ímpar

Ponha c_j para o coeficiente par original da característica completada e

\[
C_*=-\frac{\sum_{k=0}^{8}h_kc_{9-k}
+c_0\,b_{1,4}^TA_{1,4}^{-1}b_{1,4}}{10}.
\]

O novo módulo `NextSourceGate` prova, sem afirmar nenhum sinal,

\[
\operatorname{nativeSourceSchurRemainder}(1,4)=10(C_*-c_{10}),
\]

\[
c_{10}=\frac{1520I_{18}-I_{20}}{4\,20!},\qquad
I_j=\int_0^\infty u^j\theta_{\rm tail}(u)\,du.
\]

Portanto a próxima margem física equivale exatamente a

\[
\boxed{
\int_0^\infty(1520u^{18}-u^{20})\theta_{\rm tail}(u)\,du
<4\,20!\,C_*.
}
\]

Os acoplamentos antigos e a cauda assinada do integrando permanecem explícitos. A direção da desigualdade é a correspondente a c10, distinta daquela do certificado anterior para c9.

Declarações: `fifthOdd_sourceRemainder`, `source_c10_theta`, `fifthOdd_margin_iff_thetaIntegral`.

A infraestrutura certificada em `FullSourceBoxes.lean` tem hipótese de ordem menor ou igual a 18. Ela não deve ser aplicada a I20. Uma próxima rodada pode estender essa estimativa da fonte, com todas as caudas, e testar o novo limiar. Nenhuma estimativa para I20 foi adicionada aqui.

## Status

| Status | Resultado |
|---|---|
| PROVADO | Próximo pivô = metade do limite do balanço físico, em qualquer ordem fixa sob positividade do prefixo antigo |
| PROVADO | Pareamento complexo e dois cruzamentos ordenados preservados; anulação mista apenas no limite |
| PROVADO | Margem física persistente equivale ao sinal do pivô e à dominância entre os dois canais Jordan |
| PROVADO INCONDICIONAL | Margens dos quatro testes de cada paridade e do quinto teste par |
| PROVADO | Próxima margem ímpar equivale à desigualdade integral explícita com I18 e I20 |
| CONDICIONAL | Todas as margens implicam positividade das duas Hankel em toda ordem e alimentam a torre de retorno existente |
| ABERTO | Sinal do quinto teste ímpar e estimativas em toda ordem |
| NÃO AFIRMADO | Contratividade do retorno inteiro de dez fontes, novo operador, certificado HP global ou RH |

## Validação

PASS: sete módulos da rodada, 57 declarações públicas auditadas por tipos e corpos, regressões, build raiz `--wfail` com 8841 jobs e auditorias das três zonas. Todas as declarações têm somente `propext`, `Classical.choice` e `Quot.sound`.

Reprodução no servidor llm:

    bash research/critical-source-return/audit-critical-source-return.sh

O script recompila os sete módulos da rodada com avisos como erros, confere todos os nomes públicos e seus guards transitivos de axiomas por tipos e corpos, executa as regressões, o build raiz `lake build --wfail` e as auditorias Foundation, Geometry e Analysis.

Os registros finais estão em `evidence/validation.json`, `evidence/source-manifest.json` e `evidence/Audit.log`. Somente os três axiomas padrão permitidos na zona Analysis são aceitos pelo guard. Não foram introduzidos `sorry`, `admit`, axiomas, `native_decide` ou alterações de pins, métricas e amplitudes.

As dependências dos PRs anteriores são reutilizadas de seus caches compilados, com fontes e commits conferidos; não se anuncia recompilação fresca de todas essas dependências históricas. Todos os módulos novos são recompilados pelo script.
