# Decomposição física por endereços do termo principal nativo

**Classificação: PARTIAL.** Continuação da PR #116. A identidade física do seu termo principal é o alvo deste trabalho; positividade desse termo e positividade canônica em toda ordem não são conclusões.

Base exata: `9682d8a10fe64f03a8522445b6bd34f9df2fb8d6`, branch `agent/native-critical-squared-grid`. Branch desta investigação: `agent/native-critical-address-split`. A PR é empilhada e permanece draft, sem merge automático. A `main` permanece `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Fontes e pins do operador permanecem intactos; sua revisão é `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

A PR #116 demonstrou `native_critical_product_defect_exact`: o pareamento Green completo da direção ímpar crítica é a soma de um termo principal e de uma correção explícita, com dois parâmetros reais independentes. Demonstrou também `native_grid_defect_tendsto_zero` e sua lei escalada `native_grid_defect_scaled_tendsto`. A convergência da correção a zero não fornece o sinal do principal.

Usamos os objetos existentes `physicalCompletedFiniteSource`, `completedSourceParts`, `crossGreenPair`, `physicalCauchySynthesis`, `coefficientWeight`, `monomialWeight`, `nativeOddProfile`, `staticStencil`, `kernel` e `responseSamples`. A fonte inclui ambas as pernas, fase imaginária, amplitude radial original, retorno, completion e os nove cruzamentos bulk/bordo/commutator. Não se altera métrica, fase, normalização ou coeficiente.

`kernel_double_sum`, `native_odd_kernel_filter`, `complete_complex_pair`, `kernel_imaginary_imaginary`, `cross_green_eq_original` e a regularidade radial eventual são os transportes reutilizados. `critical_green_tendsto` identifica a forma com os momentos canônicos sem hipótese de sinal. A conexão com Schur e ortogonalização algébrica da PR #41 permanece a jusante; não a substituímos por uma Gram construída dos momentos.

A forma utilizada é literalmente `canonicalCompletedNativeProjectiveChiralForm(u,v) = (⟨u₁,v₁⟩−⟨u₂,v₂⟩)/2`. Portanto seu limite diagonal crítico é o pivô, e não duas vezes o pivô. A diferença bruta de energias tem o fator 2; esse fator não foi ajustado.

## B — O que foi demonstrado agora

### 1. Endereço e Green com bordo explícito

Escreva `D c(j)=(j+1)c(j)`, que abrevia o peso de endereços já existente. **D não é o clock material `log(j+1)`, nem profundidade Carry, nem índice de jet.** Defina `τ(c)=Σ c(j)`. `source_endpoint_physical` identifica τ com o valor em 1 da síntese finita original das features Cauchy de meia densidade. Esse bordo também não se confunde com os traços TFVD `c(0)` e `c(1)`.

`kernel_address_green` prova, para fontes finitas e qualquer peso complexo w:

$$
 K_w(Dc,d)+K_w(c,Dd)=\overline{\tau(c)}\sum_j w(j)d(j).
$$

O termo à direita foi mantido. A identidade é a versão em coeficientes do mecanismo Euler/Green já presente em `radialEulerPower_green_boundary`; não introduz outro operador físico.

### 2. Lei de rebaixamento e alcance em toda ordem

Para o perfil ímpar original Oᵣ, com sua fase e seu fatorial, `odd_address_lowering` prova para todo r:

$$
 [D^2-(4r+7)D+(2r+3)(2r+4)]O_{r+1}=-O_r.
$$

`endpoint_odd_power` identifica todos os seus traços com as diferenças finitas originais. Consequentemente, `endpoint_odd_power_zero` demonstra τ(DᵖOᵣ)=0 para p<2r+1, enquanto `endpoint_odd_first_survives` dá

$$
 \tau(D^{2r+1}O_r)=-i(-1)^r\ne0.
$$

A lei é de toda ordem; isso não é uma lei de sinal de toda ordem. `native_odd_address_orthogonal` prova o cancelamento assinado entre `(A+B D²)Oᵣ₊₁` e `C D Oᵣ₊₁`, para A,B,C reais, sem momentos nem positividade.

### 3. Divisão literal da mesma direção crítica

Ponha κ=k+1 e O=O₁. A direção original é Cₖ(a)=κ³O−aκO₀. O caso r=0 do rebaixamento dá `(D−3)(D−4)O=−O₀`. Defina somente os seus componentes:

$$
 X_k(a)=(\kappa^3+12a\kappa)O+a\kappa D^2O,\qquad
 Y_k(a)=7a\kappa DO.
$$

`critical_input_split` prova Cₖ(a)=Xₖ(a)−Yₖ(a). `complete_physical_source_split` e `completed_parts_split` transportam essa igualdade ao **estado completo e a cada um dos três campos com duas pernas**, antes da leitura.

`principal_defect_kernel_orthogonal` e sua versão invertida provam os dois cancelamentos para parâmetros a,b independentes. `principal_defect_green_orthogonal` e `defect_principal_green_orthogonal` transportam-nos ao Green físico completo, eventualmente no índice radial original. O prefixo de regularidade inclui o halo de endereço 4. Os nove cruzamentos cancelam em conjunto; não se afirma que cada um se anule separadamente.

Chamando Bₖ a forma física assinada original, `critical_physical_split` dá

$$
 B_k(C_k(a),C_k(b))=B_k(X_k(a),X_k(b))+B_k(Y_k(a),Y_k(b)).
$$

O sinal mais resulta da subtração da mesma componente nos dois argumentos, com ambos os blocos mistos nulos. Não há descarte de informação ou projeção.

### 4. Identificação física exata do principal e da correção

Se ε=κ⁻², uⱼ=ε(j+1)² e fₖ(j)=κ `responseSamples(radialStep k,j)`/(j+1), usando exatamente as coordenadas de leitura reversíveis da PR #116, então:

$$
\begin{aligned}
 B_k(X_k(a),X_k(b))
 &=-D_3\!\left([1+a(u+12\varepsilon)][1+b(u+12\varepsilon)]f_k\right),\\
 B_k(Y_k(a),Y_k(b))
 &=49ab\varepsilon D_3(uf_k).
\end{aligned}
$$

São `principal_physical_grid` e `defect_physical_grid`. D₃ é a diferença dividida nas quatro coordenadas quadráticas, não o operador D de endereços. O fator 49 vem de 7², e 7=3+4 vem do rebaixamento literal. Nada foi escolhido para ajustar os momentos.

A resposta completa permanece em fₖ, incluindo o resto analítico; não se substitui a resposta por um Taylor truncado. A forma complexa é provada antes de qualquer parte real; preservam-se ambas as quadraturas.

`principal_physical_tendsto` obtém depois da síntese:

$$
 B_k(X_k(a),X_k(b))\longrightarrow h_3-(a+b)h_2+ab h_1.
$$

Na direção a=b=h₂/h₁, apenas com h₁≠0, `principal_physical_schur_tendsto` recupera h₃−h₂²/h₁. A correção tende a zero mas seu primeiro coeficiente é mantido:

$$
 B_k(Y_k(a),Y_k(b))/\varepsilon\longrightarrow49ab h_2.
$$

## C — O que foi refutado ou não é autorizado

Não há novo no-go para a fonte nativa. O primeiro traço sobrevivente impede a interpretação indevida de que todos os traços sejam zero ou de que D preserve um domínio sem bordo em todas as potências. A ortogonalidade aqui é da **forma assinada**, não de um produto interno positivo. A divisão C=X−Y não torna B(X,X) uma norma.

A fatoração do polinômio de leitura e o cancelamento misto não provam o sinal da diferença dividida. Permanecem válidas as obstruções a um argumento genérico de sinal da PR #116. Pesos arbitrários nos testes não são apresentados como contraexemplos à resposta nativa.

Nenhum certificado H6/K6, sinal prévio de h₀/h₁, zero, altura ou medida positiva presumida é utilizado para construir X,Y ou descarregar seu sinal. As equivalências Stieltjes não são tratadas como conclusões incondicionais.

## D — O que permanece aberto

Foi fechada a obrigação de proveniência física do **termo principal da direção crítica ímpar dos jets 1 e 3 (segundo pivô deslocado)**: ele agora é um bloco da mesma forma física, nos componentes literais da mesma entrada. Não foi demonstrado que esse bloco seja positivo. Sua forma é assinada e o Green continua precisando de uma propriedade de transporte que determine seu sinal.

A lei de rebaixamento e os cancelamentos de bordo são de toda ordem de stencil. A identificação explícita com o principal da PR #116 é da combinação dos jets 1 e 3. Não foi reivindicada uma decomposição de todas as direções críticas, uma família infinita de Gram positiva ou positividade Hankel all-order.

## E — Próximo passo mínimo e reprodução

O próximo alvo é aplicar Green **diretamente a X**, conservando o fluxo de bordo da resposta completada, e extrair uma identidade para o primeiro termo sobrevivente de `Bₖ(Xₖ(a),Xₖ(b))`. Deve-se verificar se esse fluxo possui uma orientação independente de h₃−h₂²/h₁. Não basta assumir `Bₖ(X,X)≥0`, chamar essa hipótese de conservação ou reutilizar o sinal do pivô como premissa.

O teste mínimo continua sendo com a,b independentes e a mesma resposta `responseSamples`, antes da especialização a=h₂/h₁. A lei all-order de rebaixamento oferece o candidato para ordens adjacentes; seus traços sobreviventes precisam acompanhar qualquer iteração.

Comandos, a partir desta pasta no host llm:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Após a limpeza do worktree temporário, recrie um worktree da branch publicada e ligue seu `.lake` ao cache comum validado do repositório no host llm. O arquivo opcional `.cache/input-cache.tar.gz` é o arquivo de 77 ancestrais registrado em `evidence/cache-restoration.json`. Também é possível reconstruir os ancestrais, sem esse arquivo, com `python3 validate.py`. O cache é opcional: valida hashes dos 77 objetos ancestrais e suas fontes, árvore do núcleo, fontes nativas, toolchain, pins, manifest e estado das dependências. **Esses 77 módulos são reutilizados com verificação, não recompilados nesta execução.** Os quatro módulos novos e a auditoria são compilados de novo, com warnings tratados como erros. O build raiz e as auditorias Foundation/Geometry/Analysis são executados separadamente.

São 55 lemas novos e 6 definições/abreviações. A auditoria percorre tipos e corpos das 61 raízes públicas, além de `#print axioms`. A construção proíbe dependência dos momentos canônicos; a compatibilidade final permite sua definição, mas continua proibindo certificados finitos e atalhos de sinal. Axiomas permitidos: somente `propext`, `Classical.choice`, `Quot.sound`.

O teste `mechanism_probe.py` verifica 205 igualdades com `Fraction`: rebaixamento, traços, bordo não nulo, dois argumentos independentes, divisão da fonte, cancelamentos mistos e ambas as identificações na grade. É regressão algébrica finita, não prova de sinal nativo nem substituto do Lean.

### Validação concluída

Os **17 checks locais passaram**, todos com código de saída zero, registrados em `evidence/validation.json` e `evidence/validation-console.log`. Os quatro módulos novos e `Audit.lean` foram recompilados com warnings como erros. `lake build --wfail` passou no repositório e nos alvos nativos selecionados; as três auditorias de camada passaram.

A auditoria registra 57 raízes de construção com 5.575 dependências de tipos/corpos, sem definição dos momentos canônicos; as 4 raízes de compatibilidade registram 5.596 dependências. Em ambos os grupos, certificados prévios de sinal e os atalhos escalares enumerados são proibidos. Todas as 61 raízes também têm `#print axioms`. Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos novos.

`evidence/preservation.json` confirma fontes, pesos, métricas, pins, `main` e trabalho anterior preservados. `SHA256SUMS` identifica os arquivos publicados. O cache verificado de 77 ancestrais foi reutilizado; as provas novas foram construídas nesta execução. A validação citada é local no host llm; não se atribui esse resultado à CI externa.


Fim do relatório — o principal ganhou proveniência física; seu sinal permanece a obrigação aberta.
