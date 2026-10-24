# Média–contraste e orçamento Green: auditoria das novas notas Carry

**Resultado: PARTIAL.** Há identidades novas e uma desigualdade integral
certificadas; a positividade canônica all-order continua aberta.

24/10/2026. Repositório `thiagomassensini/geometry-of-numbers`.
Branch `agent/mean-contrast-green`, baseada na PR #82,
`79e43c991251a1219ec8c1b1901863f67d3a1d1a`.
Entrega em draft, sem merge automático. Fontes, métricas e pins preservados.

## A — O que já estava demonstrado e o que os anexos acrescentam

A PR #81 fornece as isometrias físicas de potência, refinamento comum,
pareamento com dois argumentos e jets canônicos. A PR #82 conjuga o avanço
original e o Green, mantém a reconstrução TFVD corrigida com dois bordos,
prova a igualdade das pernas residuais depois do transporte e `EE=0` na
seção regular. Os termos `BE` e `EB` são mantidos.

A PR #41 continua draft independente. Sua identidade de energia do bordo
residual = `4 ×` pivô não foi importada como se estivesse integrada e não
foi usada para supor o sinal do pivô.

Foram lidos os oito anexos, preservados seus hashes e separados três objetos:

1. O kernel periódico de câmeras ímpares `gcd(b,c)−1`, com sua fatoração
   por divisores e totientes. A lei do pivô `phi(b)` pertence a esse Gram.
2. O Gram por níveis `min(b,c)(gcd(b,c)−1)`, que conserva também o índice
   de nível. Seus pivôs não são, em geral, `phi(b)` ou `b phi(b)`.
3. O kernel canônico completado, que continua representado por um balanço
   quiral assinado e seus cruzamentos Green.

O experimento fornecido foi reproduzido. As 100 médias periódicas coincidem
exatamente com `gcd−1`, a fatoração triangular e os pivôs racionais conferem,
e a compensação do jet zero confere por quadraturas independentes dos perfis.
Isso não identifica o Gram de divisibilidade com a Hankel canônica.

O CSV Jacobi foi comparado, entrada por entrada, com o bloco do arquivo
`stage_A/N32_canonical_J.csv` do repositório `momentos`, commit
`a54f267365d5d8c965376734b17b10ae89ed3f74`. As 36 diferenças são menores
que `10⁻⁶²` (máximo aproximadamente `9,745×10⁻⁶⁴`). O PDF de três páginas
foi inspecionado visualmente e é compatível com a tabela nas precisões
exibidas. A matriz decimal **fornecida**, lida como racional exata, tem seis
pivôs positivos; isso certifica essa matriz arredondada, não intervalos da
fonte nem positividade infinita.

A nota centro–pernas ajuda a organizar os coeficientes do kernel, mas não
identifica centro de graus e centro posicional. A fatoração pontual em
quadrados não é uma Gram: seu próprio exemplo `P₁` nos pontos `0,1` tem
determinante `−1`. A ponte material continua necessária.

## B — O que foi demonstrado agora em Lean

Os nomes novos estão em `CarryMeanContrast`. Usamos o mesmo
`PhysicalCauchySpace` e o mesmo `PhysicalPair` da fonte original.

### B.1 — Média e contraste preservam o estado e a polarização

Definimos somente duas leituras lineares dos canais já sintetizados:

\[
 C_X=(X_++X_-)/2,\qquad D_X=X_+-X_-.
\]

`mean_contrast_reconstruct` recupera integralmente ambos os canais. Não
foi criada outra métrica nem identificado `C_X` com um centro inteiro.

`signed_form_mean_contrast` prova, para entradas independentes:

\[
\boxed{\Phi(X,Y)=\tfrac12(\langle C_X,D_Y\rangle+
                                    \langle D_X,C_Y\rangle).}
\]

`signed_energy_mean_contrast` dá exatamente:

\[
\boxed{\operatorname{Re}\Phi(X,X)=\operatorname{Re}\langle C_X,D_X\rangle.}
\]

`completed_equal_legs_mean_contrast` aplica essas identidades **após** a
reconstrução Green completa da #82, com seu domínio `0<eta<1` e condições
originais de regularidade no suporte finito. O residual reconstruído `E`
altera a média por `E.1`, mas não o contraste. Não é descartado como vetor.

`corrected_kernel_mean_contrast` transporta a identidade para o mesmo
`correctedGreenPairing` de duas entradas, e portanto para o kernel canônico
sob as condições de regularidade já provadas na #82.

`mean_power`, `contrast_power` e `alignment_defect_common_refinement`
mostram que as duas leituras comutam com o mesmo refinamento físico e que
o defeito de simetria abaixo é preservado por uma isometria comum.

### B.2 — A proposta D=TC tem um teste necessário mais forte que o sinal

Se `T` é simétrico e leva ambas as médias aos contrastes, é necessário:

\[
\operatorname{Re}\langle C_X,D_Y\rangle
 =\operatorname{Re}\langle D_X,C_Y\rangle.
\]

`symmetric_alignment_necessary` formaliza essa condição. A forma assinada
usa a **média simétrica** desses dois cruzamentos; sua positividade não
exige, por si só, a igualdade de cada cruzamento separado.

`normalized_chiral_mean`, `projective_mean_response` e
`projective_contrast_response` extraem as coordenadas da **fonte original**,
com os denominadores nativos não nulos. Para o vetor radial original `v_j`:

\[
 C_j=\frac2{\sqrt2}R(z_j)v_j,\qquad
 D_j=\frac{2i}{\sqrt2}v_j,
 \qquad R=-F'/(2F).
\]

Nenhum `h_n` define esses vetores. A amplitude, o retorno e o completamento
são os preexistentes; o cancelamento algébrico é feito somente depois de
ambos os canais estarem presentes.

`weighted_alignment_defect` calcula o defeito exato para pesos reais
`R(z_i)=ir`, `R(z_j)=is`:

\[
\delta_{ij}=2(r-s)\operatorname{Re}\langle v_i,v_j\rangle.
\]

`radial_cross_real_ne_zero` prova que o cruzamento das colunas radiais
originais, na mesma grade, não é zero. Logo
`no_symmetric_two_original_ports` exclui tal atribuição simétrica quando
`r≠s`, sob as condições de regularidade explicitadas no teorema.

**Alcance exato:** esse último NO-GO é condicional à desigualdade concreta
dos dois valores reais da resposta, não uma prova nesta PR de que essa
desigualdade vale em toda grade. Ele não recebe positividade de Hankel.
A condição de simetria é apenas a exigida nos dois vetores; portanto o teste
vale também para um operador real simétrico não limitado quando seu domínio
contém essas duas médias. Não se confunde isso com um teorema de domínio
ou existência de vetores-limite canônicos.

### B.3 — Uma desigualdade nova para o orçamento Green

`greenDensity eta x` é exatamente o integrando proposto nos anexos:

\[
 x^2\frac{\eta(2-\eta x)}{(1-\eta x)^2},\qquad
 J_\eta=\int_0^1\mathrm{greenDensity}(\eta,x)\,dx.
\]

`green_density_remainder` prova a identidade algébrica completa:

\[
 \mathrm{greenDensity}-(2\eta x^2+3\eta^2x^3)
 =\frac{x^2\eta(\eta x)^2(4-3\eta x)}{(1-\eta x)^2}.
\]

Para `0≤eta<1`, o resto é não negativo em `[0,1]`. Continuidade e
integrabilidade são demonstradas, sem troca de série infinita por integral.
`green_budget_lower` e `c2_green_budget_gt_half` concluem:

\[
\boxed{J_\eta\ge 2\eta/3+3\eta^2/4,\qquad J_{1/\sqrt2}>1/2.}
\]

Esta é uma desigualdade **certificada em Lean**, independente dos momentos.
Não reivindicamos nesta PR a série infinita, a fórmula com logaritmo nem os
limites separados dos setores Green. A cota resolve a obrigação de sinal de
`J` quando esses limites forem identificados com a fonte original.

## C — O que os testes excluem e o que não excluem

O diagnóstico escalar, explicitamente separado da prova Lean, avaliou a
mesma característica completada pela identificação analítica posterior com
xi. Não utilizou zeros, alturas ou momentos como entradas, nem reexecutou
inteiramente a síntese material.

Para os dois primeiros estados radiais, `kappa=k+1`, o defeito é
`delta=2*kappa*(Im R(i/kappa)−Im R(2i/kappa))/3`. Obtivemos:

| kappa | defeito real de simetria |
| ---: | ---: |
| 10 | −0,0154015943202160 |
| 100 | −0,0154033113964294 |
| 1000 | −0,0154033285701405 |

Assim, os exemplos numéricos **contrariam** o candidato que exige um único
`T` autoadjunto levando as médias desses estados finitos aos seus contrastes.
A prova formal identifica a obstrução exata quando os valores diferem; os
números não são usados para descarregar essa desigualdade no kernel.

O teste é sobre duas **portas radiais finitas**, não uma prova de que o
domínio de um operador definido somente nos jets ou numa família-limite
tenha de conter essas duas médias. Não foi provada aqui tal identificação
de domínios. Assim ele não refuta automaticamente a T4 proposta na nota.

Isso não refuta um mecanismo positivo para a forma simetrizada completa,
nem um operador que atue somente em outra família-limite cujo domínio e
existência ainda precisariam ser provados. Tampouco refuta a geometria Carry.
Não é necessário impor simetria a cada termo misto para estudar o sinal da
soma dos cruzamentos.

As fatorações por totiente têm alcance próprio. Seus pivôs não podem ser
substituídos pelos pivôs canônicos da #41; falta o transporte material fiel
entre as duas construções.

## D — O que permanece aberto

1. Os limites separados `BB/h0 → 1−2J` e `BE/h0 → J` do jet zero ainda
   não foram formalizados na fonte Green original. Provar `J>1/2` não
   descarrega automaticamente essas duas identidades de limite.
2. A desigualdade média–contraste em todas as direções canônicas continua
   aberta. Receber seu próprio sinal como hipótese seria circular.
3. Atribuir `D=TC` com `T≥0` como condição de uma ferramenta não constitui
   uma causa geométrica demonstrada. A condição de autoadjunção deve passar
   pelo teste de cruzamentos, que pode ser mais forte do que o alvo exige.
4. Não foi provada uma Gram Hilbert positiva de toda a sequência canônica,
   a independência de todos os prefixos ou a identificação unitária completa
   entre incidências multibase e o carrier refinado.
5. A ligação direta às direções residuais da #41 continua exigindo tratar
   explicitamente sua branch independente e as normalizações dos jets.

## E — Próximo passo mínimo e reprodução

Priorizar a identidade **exata em kappa finito** do termo misto do primeiro
jet, no Green original, conservando o domínio e ambos os canais. Os anexos
sugerem `BE=kappa*Im(R(2i/kappa)−R(i/kappa))*J_eta`.
Uma vez demonstrada essa igualdade, a derivada central original deve dar
o limite e a cota de B.3 resolve seu sinal. Não é necessário começar por
um operador autoadjunto médio–contraste que imponha uma condição extra.

Em paralelo conceitual, para uma futura lei all-order, procurar uma
identidade do fluxo que controle **a parte simetrizada completa** dos
cruzamentos, incluindo nativo, Gamma e bordos. Sua origem física precisa
ser demonstrada antes de aplicar os consumidores Gram/Jacobi.

Os módulos novos são `MeanContrast.lean`, `AlignmentTest.lean`,
`GreenBudget.lean`; `Audit.lean` contém `#print axioms` e inspeção transitiva
de tipos e corpos. Nenhum momento ou sinal canônico define a construção.
Vinte módulos ancestrais foram recompilados a partir de fontes imutáveis.

**Validação executada:** 24 teoremas, cinco definições e uma abreviação;
30 raízes públicas e 5.765 dependências transitivas de tipos e corpos.
Somente `propext`, `Classical.choice` e `Quot.sound`; sem novos axiomas
matemáticos, `sorry`, `admit` ou `native_decide`. As 14 verificações passaram,
incluindo os módulos explícitos, `lake build --wfail`, auditorias separadas
Foundation/Geometry/Analysis, preservação da base e diagnóstico Python
separado. As fontes e os arquivos preexistentes do operador foram preservados.

Comandos no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

O diagnóstico dos anexos usa o Python Miniforge existente. O programa do
usuário é carregado como módulo e suas funções são executadas sem acionar
a escrita original em `/mnt/data`. Os arquivos originais são preservados.
Hashes, comandos, auditorias e resultados estão em `evidence/`.
A confiança Lean é independente dos diagnósticos Python.

**FIM DO RELATÓRIO — média–contraste e cota J certificadas; alinhamento simétrico testado com escopo explícito; Gram positiva canônica all-order aberta.**
