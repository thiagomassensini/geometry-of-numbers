# Câmeras, informação material e quociente da leitura Green

## Resultado

**PARTIAL — separação material finita e defeito físico de um quociente específico formalizados. A forma positiva dos momentos canônicos em todas as ordens permanece OPEN.**

A investigação produziu um resultado construtivo: uma única família de observações das câmeras originais distingue todos os dados materiais de suporte finito, com coeficientes complexos. Para suporte nos endereços `1,...,N`, bastam exatamente `N` câmeras: `2N+1` e `4,6,...,2N`. A separação foi provada para todo `N`, sem usar momentos, pivôs ou positividade.

Também foram demonstradas duas obstruções específicas. A norma das sondas geométricas entre câmeras não desce pela mera igualdade das respostas escalares completadas. Além disso, o representante de norma mínima obtido pela projeção ortogonal do readout seed+retorno geralmente viola a relação física entre interior e retorno. O defeito foi calculado exatamente, sem substituir a fonte, a métrica ou o retorno.

Não foi encontrada uma representação Gram positiva do balanço Green completado. Os novos resultados distinguem redundância de representação, invisibilidade escalar e perda de proveniência; não resolvem o sinal global por renomear uma condição de positividade.

## Base, escopo e preservação

- Repositório editado: `geometry-of-numbers`, no host `llm`.
- Base e `origin/main`: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, conferidos antes da edição.
- Branch: `agent/carry-quotient-green-coherence`, criada da base limpa; os PRs #34–#38 não foram alterados nem incorporados.
- Checkout inicial: `agent/carry-scale-covariance`, `16de0ef478afb1c95c16edfe8153ac80dc035b71`, limpo e preservado em sua branch.
- Operador consultado: `carry-self-adjoint-operator`, `bfeb10fd2425400fa38139903d12bf0599f02e53`. Não houve edição; os dois arquivos de usuário não rastreados foram preservados e tiveram seus hashes conferidos.
- Dependência nativa efetivamente usada na compilação cruzada: `NativeCarrySpectralWeyl`, pin `298d83c9351e308a5213b9f5ac32e44087f98a9f` do operador. O checkout separado da investigação relacional também foi consultado, sem alteração.
- Nenhuma alteração de pins, fonte, amplitude, fase material, endereço, métrica, câmera, dressing ou normalização. As novas definições de pesquisa apenas observam os perfis já existentes.
- Nenhum worktree criado, removido ou alterado. Sem merge automático, conforme a instrução do usuário.

A Foundation permanece congelada. O módulo novo da biblioteca pertence a Analysis; as comparações entre repositórios permanecem em módulos de pesquisa, compilados explicitamente no ambiente cruzado existente.

## 1. Resultado construtivo: as câmeras distinguem a informação material finita

Para coeficientes complexos `a(n)` nos endereços materiais positivos `1,...,N`, foram reutilizados literalmente os perfis nativos `profile b n`. Não há identificação entre endereço material, profundidade e ordem de jet.

Defina apenas as observações:

\[
O_b(a)=\sum_{n=1}^{N}a_n\,\operatorname{profile}_b(n),\qquad
T=\sum_{n=1}^{N}a_n,\qquad
A_d=\sum_{\substack{1\le n\le N\\d\mid n}}a_n.
\]

Os perfis originais dão as identidades exatas

\[
O_{2N+1}(a)=T,
\]

\[
\boxed{O_{2d}(a)=T+A_d-(2d+2)A_{2d},\qquad 2\le d\le N.}
\]

Como `A_d=0` para `d>N`, as observações determinam os `A_d` por eliminação descendente. Depois,

\[
a_d=A_d-\sum_{\substack{k\ge2\\kd\le N}}a_{kd}
\]

determina os coeficientes materiais por outra eliminação descendente. A prova Lean usa essas duas estruturas triangulares para demonstrar que observações nulas obrigam todos os coeficientes a serem nulos. Nenhuma desigualdade de sinal entra na prova.

Teoremas novos, em `research/carry-quotient-green-coherence/MaterialCameraSeparation.lean`:

- `odd_camera_total`;
- `even_camera_divisibility`;
- `divisibility_above_support`;
- `divisor_readouts_zero`;
- `divisibility_separates`;
- **`finite_camera_separation`**;
- `bounded_readout_eq`;
- **`all_cameras_finite_separate`**;
- `finiteMaterialObservation_sub`;
- **`all_cameras_finite_injective`**.

As duas últimas conclusões de separação aplicam-se à mesma observação `finiteMaterialObservation`, definida em `ℕ →₀ ℂ`, com coeficiente zero no endereço zero. Portanto, não se trata de escolher uma realização diferente para cada dimensão. `bounded_readout_eq` identifica o cálculo por prefixo com essa única família em todo suporte finito.

Isso resolve uma obrigação específica de informação: no domínio de suporte finito, nenhuma contribuição material independente pode ser anulada por todas as câmeras. **Não demonstra isometria, uma norma global selecionada por essas observações, nem uma igualdade com a Hankel canônica.** Tampouco demonstra continuidade ou separação da fonte infinita completada. A reconstrução TFVD já existente não foi reaberta nem substituída.

## 2. Mesma resposta escalar não significa o mesmo vetor geométrico

O módulo `CameraObservation.lean` compara objetos já existentes, sem identificar suas naturezas.

Para as sondas `cameraVector` das câmeras 2 e 4, a Gram nativa dá

\[
\langle v_2,v_2\rangle=6,\quad
\langle v_2,v_4\rangle=\langle v_4,v_2\rangle=10,\quad
\langle v_4,v_4\rangle=22.
\]

Consequentemente,

\[
\boxed{\|v_2-v_4\|^2=8.}
\]

Por outro lado, `normalizedCompletedNativeCameraCharacteristic_eq`, já existente no operador, prova que as duas respostas completadas, com seus fatores de câmera originais removidos pela construção preexistente, são exatamente iguais para todo cutoff.

`no_camera_energy_descent` demonstra que nenhuma função quadrática — de fato, nenhuma função de energia que valha zero em zero — pode preservar essa norma das diferenças passando apenas pela diferença dessas respostas escalares. O argumento já falha em duas câmeras, com igualdade racional exata.

**Alcance:** as sondas de câmeras não são automaticamente o mesmo estado escrito em duas bases. Este resultado refuta o quociente específico que declararia `v₂-v₄` uma redundância apenas pela coincidência das respostas completadas. Não refuta uma verdadeira mudança de coordenadas do mesmo estado físico, com mapas de compatibilidade demonstrados.

## 3. O quociente ortogonal do readout e seu defeito de bordo

No carrier material original, escreva

\[
y=(s,g,r),\qquad \ell(y)=s+r.
\]

A métrica é o produto Hilbert existente. A projeção de readout já definida no projeto é

\[
P_\ell y=\left(\frac{s+r}{2},0,\frac{s+r}{2}\right),
\qquad Q_\ell=I-P_\ell.
\]

A polarização existente foi usada para provar

\[
\boxed{\|y\|^2=\frac12|\ell(y)|^2+\|Q_\ell y\|^2.}
\]

`carryMaterialReadout_unique_minimum` identifica `P_ℓ y` como o **único minimizador ambiente** da norma entre todos os vetores com o mesmo readout. O fator `1/2` é forçado pelo readout e pela métrica originais; nenhum ajuste foi feito.

Para famílias finitas de coeficientes complexos, `carryMaterialReadout_finite_energy` demonstra

\[
\left\|\sum_i c_i y_i\right\|^2
=\frac12\left|\sum_i c_i\ell(y_i)\right|^2
+\left\|\sum_i c_iQ_\ell y_i\right\|^2.
\]

Todos os cruzamentos permanecem dentro das somas vetoriais antes da energia. `carryMaterialReadout_complete_injective` prova que guardar o readout **junto** do complemento é uma codificação injetiva do estado completo.

Entretanto, o domínio físico `D` do clock exige, entre outras condições,

\[
r=\sum_{k\ge0}\bigl(g(4k+3)-g(4k+2)\bigr).
\]

A projeção ambiente tem interior zero. Seu defeito exato é

\[
\boxed{\operatorname{return}(P_\ell y)
-\sum_k\operatorname{cellReturn}_k(P_\ell y)=\frac{\ell(y)}2.}
\]

Por isso,

\[
\boxed{P_\ell y\in D\iff\ell(y)=0.}
\]

Para `y∈D`, o complemento carrega o defeito oposto,

\[
\operatorname{return}(Q_\ell y)
-\sum_k\operatorname{cellReturn}_k(Q_\ell y)=-\frac{\ell(y)}2,
\]

e `Q_ℓ y∈D` também equivale a `ℓ(y)=0`. A soma dos dois pedaços recupera o estado físico original; os pedaços ortogonais geralmente não são estados admissíveis separadamente.

`carryMaterialReadout_source_projection_not_physical` descarrega todas as hipóteses para a fonte efetiva `baseTwoCompletedBoundaryHilbertState 0`: sua projeção ambiente não pertence ao domínio do clock. `carryMaterialReadoutProjection_not_isometric_domain` mostra que um transporte complexo linear isométrico não pode fazer esse representante virar a imagem de um estado de `D`.

**Não foi provado** que o ínfimo restrito a `D` coincida com o mínimo ambiente, nem que exista ou inexista outro minimizador restrito a `D`. A conclusão demonstrada é a inadmissibilidade deste minimizador ambiente e o defeito explícito que a causa.

Isso não invalida o ledger Green anterior: ele é uma identidade algébrica válida no carrier ambiente. A nova prova impede promovê-lo automaticamente a uma decomposição em evoluções físicas independentes. A projeção central `carryMaterialCentralComplement`, que já preserva o domínio, é outro mapa; sua preservação de domínio não foi confundida com a projeção de readout.

## 4. O ataque ao sinal e a obrigação que restou

A fonte física efetiva continua sendo

\[
Y(t)=\texttt{baseTwoCompletedBoundaryHilbertState}(t),\quad
Z(t)=D(t)Y(t),\quad C(t)=(-Z'(t),2Z(t)).
\]

O teorema existente `CarryMaterialGreenPairComparison.material_pair_corrected_green` identifica o Green físico menos o Green do complemento de readout com o Wronskiano completado da mesma fonte. `material_clock_canonical_residual_ledger` retém central/central, compressed/compressed, os dois cruzamentos compressed/forcing, forcing/forcing e o complemento escondido.

Foram confrontadas duas tentativas de extrair positividade dessa arquitetura:

1. **Identificar respostas escalares iguais e descer a norma entre câmeras:** refutada pela distância quadrática 8.
2. **Usar o minimizador ortogonal do readout como estado físico redundância-livre:** refutada pelo defeito de bordo `ℓ(y)/2` e pela falha de domínio para a fonte efetiva.

A alternativa de guardar o complemento conserva a informação e a norma, mas mantém o balanço Green assinado; não elimina sua obrigação de sinal. A alternativa de usar a projeção central que preserva o domínio já possui testes de primeiro jet na investigação existente, incluindo `material_centered_firstJet_ne_canonical` e `material_centered_not_residual_diagonal_germ`. Não foi anunciada como nova realização positiva.

O resultado do PR #37 foi consultado sem ser incorporado como dependência. Nele, a energia forcing–forcing é `−h₀‖Σ cᵢv(tᵢ)‖²`; seu complemento físico restante `𝓡` satisfaz uma identidade exata de Schur. A obrigação continua sendo provar, dos mesmos canais físicos,

\[
\operatorname{Re}\sum_{i,j}\overline{c_i}\mathcal R(t_i,t_j)c_j
\ge h_0\left\|\sum_i c_i v(t_i)\right\|^2.
\]

Esta rodada não demonstrou essa desigualdade. A nova separação entre câmeras não autoriza assumir o sinal de `𝓡`, e a retirada de um vetor fisicamente observável não é uma eliminação legítima de mera redundância.

## 5. Respostas A–E

**A. Qual objeto físico existente pode produzir os momentos?** O mesmo estado material completado e vestido e seu par companheiro/valor `carryMaterialCompanionValuePair`, cuja leitura é `(-F′,2F)`. A ligação assinada com a resposta logarítmica já existe; uma realização Hilbert positiva dessa leitura ainda não foi construída.

**B. Qual igualdade exata falta?** Uma fatoração física positiva, com todos os termos de bordo, retorno e dressing, do kernel real original `carryMaterialRealKernel` — equivalentemente, do residual com o centro corretamente recomposto. Depois da extração dos jets, isso deve dar os pareamentos `h_(i+j)` e `h_(i+j+1)` da mesma sequência canônica. A coincidência de respostas entre câmeras e a injetividade do observador não são essa igualdade bilinear.

**C. Houve avanço?** Sim: a separação de todos os dados materiais de suporte finito foi provada a partir das câmeras originais; a relação entre mínimo ambiente e domínio físico foi resolvida, com defeito exato. Duas realizações específicas foram excluídas. A obrigação de sinal do kernel completado não foi enfraquecida por uma nova hipótese nem descarregada.

**D. O que está no kernel?** Os 32 teoremas novos e as seis definições de observação da pesquisa foram compilados e auditados. A separação é válida para todo tamanho finito, incluindo coeficientes complexos. A identificação dos momentos com uma Gram positiva em todas as ordens, a extensão desse observador à fonte infinita e uma norma global invariante com as quatro propriedades pedidas continuam abertas. Os determinantes unitários do script são regressões racionais finitas; não há teorema Lean novo afirmando a fórmula do determinante para toda ordem.

**E. Próximo passo matemático mais curto?** Procurar uma identidade de Green/Bessel para o restante físico que preserve o domínio, ou uma fatoração do mesmo kernel completado por um estado de bordo/retorno cuja admissibilidade e pareamentos possam ser demonstrados. Os novos lemas fornecem testes imediatos: conservar as observações materiais finitas, verificar a relação retorno–interior e comparar o kernel polarizado completo. Não reabrir reconstrução TFVD nem redefinir uma métrica para forçar a igualdade.

Os certificados H6/K6 e a realização física de doze fontes permanecem resultados finitos anteriores. Não foram usados para definir o observador, a projeção ou a fonte desta investigação; também não provam a existência do quociente global desejado.

## Validação e reprodução

Novos módulos:

- `GeometryOfNumbers/Analysis/CarryMaterialReadoutQuotient.lean`;
- `GeometryOfNumbers/Analysis/CarryMaterialReadoutQuotientAudit.lean`;
- `research/carry-quotient-green-coherence/MaterialCameraSeparation.lean`;
- `research/carry-quotient-green-coherence/CameraObservation.lean`;
- `research/carry-quotient-green-coherence/Audit.lean`.

O registro da biblioteca contém somente o import novo e os comandos de auditoria obrigatórios. `public-roots.json` enumera as 38 raízes: 18 teoremas da biblioteca e 20 declarações da pesquisa. A auditoria percorre tipos e corpos transitivamente, além de `#print axioms`, permitindo apenas `propext`, `Classical.choice`, `Quot.sound`. Os fechamentos encontrados foram 3.481 declarações na biblioteca e 4.972 na pesquisa. Sem `sorry`, `admit`, `native_decide`, definições opacas ou axiomas matemáticos novos nos módulos de prova novos.

```bash
python3 research/carry-quotient-green-coherence/check_sources.py
python3 research/carry-quotient-green-coherence/validate.py
python3 research/carry-quotient-green-coherence/verify_evidence.py
```

`validate.py` registra onze comandos: fontes; build focado com `--wfail`; os dois módulos de pesquisa e sua auditoria explícita com warnings como erros; regressão racional; build de raiz com `--wfail`; auditorias Foundation/Geometry/Analysis; `git diff --check`. Os resultados e os hashes dos logs comprimidos ficam em `evidence/validation.json`.

`proof-source-manifest.json` registra os hashes dos sete arquivos Lean novos ou modificados, conferidos novamente por `verify_evidence.py`. `source-manifest.json` registra os arquivos anteriores consultados e preservados; os dois arquivos de usuário não rastreados são verificações de preservação específicas deste host, não dependências das provas.

A regressão usa os mesmos perfis, sem momentos como entrada. Nas ordens `1,2,3,4,6,12,24,32`, verifica determinante exatamente 1 e recuperação exata de duas quadraturas racionais. Essa execução acompanha, mas não substitui, a prova Lean de separação para todo `N`.
