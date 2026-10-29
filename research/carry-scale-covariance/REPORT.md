# Lei de escala Carry, Cholesky/Jacobi e alturas

## Resultado

**PASS da covariância algébrica em ordem arbitrária. PARTIAL da ponte física; síntese completada ainda OPEN.**

A lei do teste foi formalizada para todo tamanho finito, usando os objetos existentes. O aprofundamento identificou três distinções exatas:

1. O Jacobi cancela a massa global `α`. Portanto duas sequências diferentes podem ter o mesmo Jacobi e as mesmas alturas sob o transporte coerente.
2. Multiplicar a característica por uma constante não muda os momentos da derivada logarítmica. Reparametrizar a resposta em `u=t²` produz **`h′ᵣ=q^(r+1)hᵣ`**, isto é, fixa `α=q` nessa operação.
3. Dilatar endereços materiais por `n↦qn` produz amplitude `q^(-1/2)` e uma fase comum `exp(-it log q)`. Isso é uma translação da frequência material por `log q`, e não a reparametrização temporal que aparece na lei dos momentos.

Nenhum desses resultados prova positividade canônica all-order. A escala positiva preserva sinais existentes e não cria os sinais que ainda faltam.

## Proveniência e escopo

Repositório editado: `geometry-of-numbers`, no host `llm`. Base `origin/main` confirmada em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Branch `agent/carry-scale-covariance`, separada dos PRs #34–#37. Sem merge automático.

O operador foi consultado em `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem alterações. Os dois arquivos não rastreados do usuário foram preservados e têm hashes conferidos. Não se alteraram fonte, métrica, amplitude, câmera, dressing, retorno, definições históricas ou pins. Não foram criados worktrees; os anteriores foram preservados.

O arquivo fornecido pelo usuário foi lido como teste e contexto, sem tratar seus comentários como instruções adicionais. Sua cópia íntegra é [reference_test.py](reference_test.py). O SHA256 e a execução exata estão em `evidence/reference-local.json`.

| Operação | Consequência demonstrada |
| --- | --- |
| Multiplicar a resposta por uma constante não nula | Os momentos logarítmicos não mudam |
| Substituir `u` por `qu` na resposta | `h′ᵣ=q^(r+1)hᵣ`, portanto `α=q` |
| Dilatar os endereços materiais `n↦qn` | Fator pontual `q^(-1/2)exp(-it log q)`; síntese completada ainda por transportar |
| Trocar câmera normalizada | Mesmos momentos; uma descrição por `αq^r` força `α=q=1` |
| Aplicar abstratamente `h′ᵣ=αq^rhᵣ` | `J′=qJ` e `T′=q^(-1/2)T` no transporte coerente; `α` cancela |

## 1. Geometria: amplitude, duas pernas e endereço

Arquivo: `CarryScaleGeometry.lean`, namespace `GeometryOfNumbers.Analysis.CarryScale`.

O teorema `amplitude_eq_inverse_sqrt_depth` reutiliza a fundação de massa já encerrada e prova

\[
\operatorname{realCriticalAmplitude}(b,k)
=\frac1{\sqrt{b^k}}=b^{-k/2},\qquad b>0.
\]

Não se seleciona novamente o expoente usando o operador espectral. O operador continua downstream da fundação.

Para a leitura original `realCenteredReadout`, `centered_inverse_sqrt_dilate` prova

\[
\Delta_{qa}^2 f(qC)=q^{-1/2}\Delta_a^2f(C),\qquad f(x)=1/\sqrt x,\quad q>0.
\]

`centered_relative_defect_dilate` prova a invariância do defeito relativo. `centered_relative_defect_shape` explicita sua dependência apenas de `a/C`:

\[
\frac{\Delta_a^2f(C)}{f(C)}
=\frac1{\sqrt{1-a/C}}+\frac1{\sqrt{1+a/C}}-2,\qquad C>0.
\]

Para a interpretação física das três posições exige-se `C>|a|`, de modo que ambas as pernas sejam positivas. As identidades Lean usam a extensão total de `Real.sqrt`; isso não amplia o domínio físico das posições.

O resultado de proveniência é `material_sample_dilate`, sobre a amostra original `criticalMaterialSample`, para endereços naturais positivos:

\[
\boxed{\quad f_t(qn)=q^{-1/2}e^{-it\log q}f_t(n).\quad}
\]

`material_three_addresses_dilate` transporta o mesmo fator em **três endereços ordenados independentes**, mantendo as duas pernas e o centro. Não identifica dilatação com troca de câmera, nem soma apenas amplitudes descartando a fase.

Ainda não se demonstrou que a dilatação de toda a geometria, com seus índices, cabeça, cauda, retorno e completion, transporta a característica canônica por uma ação determinada. O resultado pontual não é anunciado como essa síntese completa.

## 2. Mesma ação scaledMoment, com massa explícita

`massScaledMoment α q h` é literalmente `α * scaledMoment q h`, usando a definição **já existente** em `FiniteClockHeightLedger`. O módulo de pesquisa prova `scaledMoment_native_eq`: a convenção local e a do operador são iguais por definição. Não se substitui a sequência canônica por esta sequência transformada.

`scaled_hankel` e `scaled_shifted` provam, para todo `N`,

\[
h'_r=\alpha q^r h_r,
\quad D=\operatorname{diag}(q^i),
\quad G'=\alpha DGD,
\quad K'=\alpha qDKD.
\]

Essas duas identidades são puramente algébricas; não requerem positividade. Para os teoremas de Cholesky real e preservação de sinais, `α>0` e `q>0` são condições explícitas.

## 3. Eliminação e Cholesky determinístico em qualquer ordem

Arquivo: `MomentScaleElimination.lean`. A recorrência reutilizada é `carryPairingRemainder`, e não uma inversa numérica.

`elimination_scale` prova, mais geralmente, para diagonais não nulas,

\[
R'_n(i,j)=\alpha d_i d_jR_n(i,j).
\]

A prova conserva todos os cruzamentos e inclui os pivôs nulos: nesse caso permanece a convenção totalizada já existente, sem inferir que a linha desaparece. Não se transforma um pivô zero em invertibilidade.

`pivot_scale`, `column_scale` e `cholesky_scale` transportam os objetos **determinísticos existentes**. Em particular, `hankel_cholesky_scale` prova

\[
\boxed{L'=\sqrt\alpha\,DL.}
\]

Aqui `L=carryPairingCholesky`. Quando os pivôs anteriores são positivos, o teorema anterior `carryPairingCholesky_identity` prova que esse objeto é um fator de Cholesky verdadeiro, triangular inferior com diagonal positiva. Sem tais sinais, ele continua sendo o candidato assinado com defeito explícito do módulo original; esta rodada não apaga seu defeito.

`sector_pivot_scale` mantém também o deslocamento original dos setores:

\[
p'_{s,r}=\alpha q^{2r+s}p_{s,r}.
\]

`hankel_pivot_sign` prova preservação do sinal estrito no setor não deslocado. A fórmula geral fornece o mesmo para os demais setores quando o fator é positivo. `pivot_ratio_invariant` prova a invariância de `p_(r+2)p_r/p_(r+1)^2`. Sua interpretação como razão ordinária exige denominador não nulo; a igualdade Lean também cobre a divisão totalizada em zero.

## 4. Jacobi, inversa do Cholesky e operador matricial de alturas

Arquivo: `MomentScaleHeight.lean`. O whitening transportado é

\[
B'=\alpha^{-1/2}BD^{-1}.
\]

`scaled_whitening` demonstra sua identidade de Gram. `cholesky_inverse_scale` demonstra que esse é **o inverso matricial efetivo do Cholesky escalado** quando os pivôs do bloco original são positivos. Portanto não se presume a fórmula da inversa nem se aceita um fator independente ajustado.

`jacobi_scale`, `jacobi_section_scale` e `cholesky_jacobi_scale` provam

\[
\boxed{J'=qJ.}
\]

A igualdade aplica-se ao inverso do Cholesky e à definição existente `finiteJacobiSection` com o whitening coerentemente transportado. Não se anuncia uma igualdade definicional entre esse transporte e uma escolha independente de whitening. A definição separada `canonicalFiniteJacobiSection` por LDL não foi reescrita nesta rodada.

Para **toda matriz finita positiva definida** `J` e `q>0`, `finite_height_scale` prova, no cálculo funcional matricial existente,

\[
\boxed{\operatorname{finiteHeightOperator}(qJ)
=q^{-1/2}\operatorname{finiteHeightOperator}(J).}
\]

`native_finite_height_scale` e `native_jacobi_scale` aplicam as igualdades aos símbolos originais de `carry-self-adjoint-operator`, por compatibilidade definicional com as realizações locais. A positividade de `qJ` é deduzida da de `J`; não é uma hipótese adicional. A igualdade é do operador inteiro, não apenas de uma lista de autovalores ou de alturas escolhidas.

`finite_height_depth_scale` especializa `q=b^k` e identifica literalmente o fator com `realCriticalAmplitude b k hb`. Esta é a ligação formal entre as duas leis de meia escala **depois de especificar a transformação algébrica de J**. Não é uma prova de que a dilatação física induz essa transformação.

### A massa global se perde no passo espectral

`jacobi_mass_blind` prova que, fixado `q`, toda massa positiva `α` dá o mesmo `qJ` sob o transporte coerente. No módulo nativo, `native_geometric_mass_not_response_dilation` e `native_two_mass_actions_same_jacobi` combinam dois fatos:

\[
q^{-1}q^rh_r\ne q\,q^rh_r\quad(q\ne1),
\]

mas ambas as ações dão o mesmo Jacobi escalado. Portanto o teste de alturas não determina qual dessas duas transformações dos momentos foi realizada.

## 5. O fator fixado pela derivada logarítmica

Arquivo: `LogDerivativeScale.lean` e comparação nativa `NativeScaleSeam.lean`.

A sequência canônica é extraída da resposta por derivada logarítmica, não de massas espectrais escolhidas. Usando a recorrência original division-free e sua unicidade, `log_moments_dilate` prova em toda ordem:

\[
\phi'_n=\beta q^n\phi_n,\quad\beta\ne0,\quad\phi_0\ne0
\quad\Longrightarrow\quad
\boxed{h'_r=q^{r+1}h_r.}
\]

É a substituição `u↦qu` na resposta, com `u=t²`. A constante `β` cancela e o fator adicional `q` vem da derivada.

`native_log_moments_dilate` aplica a lei às definições **originais** `completedNativeRealEvenCharacteristicCoefficient` e `canonicalCompletedNativeLogDerivativeMoment`, sem assumir sinal Hankel. `native_log_moments_constant_amplitude` prova que apenas multiplicar a resposta por uma constante não muda esses momentos.

Assim, escolher `α=q^(-1)` no teste algébrico é legítimo, mas isso não é consequência de multiplicar a característica pela amplitude geométrica. Para a reparametrização simples da resposta o fator correto é `α=q`. `geometric_mass_not_response_dilation` refuta a identificação dessas duas ações quando `q≠1` e `h₀≠0`.

O teorema `log_response_phase` mantém outro efeito que não pode ser descartado: se um fator não nulo tem derivada `g'=-iωg`, então, onde a resposta não se anula,

\[
-\frac{(gF)'}{2gF}=-\frac{F'}{2F}+\frac{i\omega}{2}.
\]

Não se afirma que a dilatação da síntese completada inteira seja essa multiplicação. A lei pontual material mostra por que o transporte da fase e do completion precisa ser demonstrado.

## 6. Câmeras normalizadas: rigidez demonstrada

O resultado anterior `completedNativeCameraUniversality` já afirma igualdade exata dos momentos entre câmeras normalizadas. Não foi usado como se afirmasse uma dilatação.

`native_camera_scale_rigid` acrescenta uma consequência nova, usando apenas os sinais de baixa ordem já certificados: se a ação `αq^r` identifica duas dessas sequências de câmera, então

\[
\boxed{\alpha=1,\qquad q=1.}
\]

Bastam `h₀≠0` e `h₁≠0`. Assim, uma mudança de câmera normalizada não pode realizar uma dilatação não trivial desta forma. Isso não exclui uma operação física de dilatação distinta da mudança de câmera.

## 7. Próxima obrigação física mínima

É preciso construir a operação sobre o **estado original completo**, com endereço, pernas, fases, cabeça, cauda, retorno e dressing, e calcular seu response `F̃` antes de extrair momentos.

Uma identidade suficiente a procurar, e ainda não demonstrada da geometria, é

\[
\widetilde Q(t)=\frac{\alpha}{\sqrt q}\,Q(\sqrt q\,t).
\]

Ela deve ser consequência da síntese construída, não definição de uma nova fonte para obter os momentos desejados. Na variável `u=t²`, a obrigação correspondente pode ser escrita sem dividir pela característica:

\[
\widetilde\Phi'(u)\Phi(qu)
=\alpha\widetilde\Phi(u)\Phi'(qu).
\]

A tentativa de usar apenas amplitude constante já é excluída pelo cancelamento da derivada logarítmica. A reparametrização simples já está resolvida e fixa `α=q`. Uma dilatação de endereços tem, na amostra original, a fase comum demonstrada. A tarefa restante é identificar o transporte efetivo **completado**, distinguindo essas operações.

## 8. Validação e reprodução

São **41 teoremas públicos novos**, 33 de biblioteca e oito de comparação nativa, e quatro definições de observação/transporte. Todas as 45 raízes têm `#print axioms` e guard transitivo de tipos/corpos, permitindo somente `propext`, `Classical.choice`, `Quot.sound`. O inventário exato está em `public-roots.json`.

Os comandos reproduzíveis de Lean são:

```bash
python3 research/carry-scale-covariance/check_sources.py
python3 research/carry-scale-covariance/validate.py
python3 research/carry-scale-covariance/verify_evidence.py
```

`validate.py` executa nove checks no `llm`: hashes/preservação; build focado com `--wfail`; compilação explícita da comparação nativa e sua auditoria com warnings como erros; build de raiz com `--wfail`; auditorias Foundation/Geometry/Analysis; `git diff --check`. Sem dependências ou pins novos.

O teste simbólico fornecido foi executado **no desktop local**, com o Python/SymPy já instalados. O `python3` padrão do `llm` não tem SymPy; não se instalou dependência para repetir o mesmo teste. Em uma instalação com SymPy:

```bash
python3 research/carry-scale-covariance/reference_test.py
```

O teste N=3 usa massas e três valores espectrais sintéticos, não os momentos canônicos, zeros ou alturas da zeta. Seu sucesso é um teste algébrico finito separado das provas em ordem arbitrária. O log exato, versões e SHA256 estão em `evidence/reference-local.*`.

`source-manifest.json` registra as fontes novas e reutilizadas e os arquivos preservados do operador. `evidence/validation.json` registra os checks remotos e hashes dos logs. `VALIDATION.md` registra o resultado final e as dimensões dos fechamentos auditados. O commit e a URL do PR constam da entrega local. Sem merge automático.
