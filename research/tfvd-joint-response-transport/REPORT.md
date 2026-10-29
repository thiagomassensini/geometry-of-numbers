# Transporte e extração conjunta do numerador TFVD completado

**Resultado: PARTIAL.** A sugestão de compor defeitos foi testada na fonte original. Foi demonstrada uma composição determinantal sem divisão por cabeças e construída sua versão polarizada, com ambos os cruzamentos logarítmicos, Xi, chart e caudas exatas. O pareamento físico completo foi identificado com esse numerador e transportado à direção fixa da PR #41. Todos os coeficientes canônicos são recuperados do mesmo germ polarizado. **Não foi obtida uma nova lei independente de sinal, nem positividade Hankel all-order.**

Base: `008e77c6a052d3b561370f3d6f5667e3067b94e2`, HEAD da PR #65.
Branch: `agent/tfvd-joint-response-transport`.
Repositório/host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
Entrega empilhada sobre `agent/tfvd-critical-two-port-ledger`, em draft, sem merge automático. O operador foi consultado em `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem modificações. Não foram criadas worktrees nem alterados pins, fontes, câmeras, métricas ou arquivos anteriores.

O texto fornecido em `c62ee29d-4681-417c-ae22-9182ff0c4d35/Texto colado.txt` foi tratado como proposta de investigação, não como prova ou autorização para postular uma realização Gram. Seu foco em defeitos compostos orientou o teste. A nota `materialJet_pairing` é correta, mas não remove o no-go específico da PR #36 para a identificação direta dos momentos com energias Krylov do clock material.

## A — O que já estava demonstrado

1. `tfvdCanonicalResponse_eq_original` e `tfvdCanonicalResponse_regular_denominators`, em `NativePhysicalTfvdSecondPort.lean`, identificam o produtor TFVD completo com a resposta original na seção regular. A regularidade recai nos valores **completos**, não nas cabeças.
2. `canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed` e `...logJetReadout_eq_completed`, em `CompletedC3BracketTfvdGreenFactorization.lean`, conservam simultaneamente as duas caudas. `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime` identifica os dois traços com `(F,-F')`.
3. `twoPort_signed_form`, em `NativePhysicalTwoPortChart.lean`, calcula a forma assinada original das duas pernas na métrica Cauchy. `physicalEndpointJetInput_decode` recupera as coordenadas materiais do mesmo input de endpoint.
4. A PR #65 fornece `CarryTfvdCritical.fullSource_eq_original`, `fullSource_eventually_eq_original`, `full_head_polarized_ledger` e `critical_total_flux_tendsto`. A soma de cabeça e correção já converge ao pivô, sem premissa sobre seu sinal.
5. A PR #41, commit imutável `ee56930a2c30456cfbd214a29bb31b12d3977204`, fornece `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy`. O requisito é `IsUnit` do prefixo; não se recebe positividade do pivô novo.
6. `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical`, em `CompletedNativeTfvdWronskianMoments.lean`, fornece a identificação de toda ordem dos coeficientes. `hasDerivAt_completedNativeLogDerivativeHerglotzCoordinate_zero`, em `CompletedNativeChiralCayleyHerglotz.lean`, já identifica a primeira derivada com `2h₀`, sem resolver a positividade global do kernel Herglotz.
7. `sourceCoordinatePair_jet_signed_defect_expansion`, em `ChiralLogGapDefectTransport.lean`, preserva os quatro setores do comutador material. Os gates `hasNativePolarizedCoefficientVectorEquation_iff_correctedChiralFirstColumnGram_of_transport` e `...iff_sixAnalysisJet_of_transport` continuam condicionais à família Hilbertiana e à sua identidade de transporte. Nenhum deles descarrega sozinho a primeira coluna física.

As reduções abstratas anteriores não foram rebatizadas como provas de positividade. Não se reabriu a reconstrução TFVD já certificada nem se reconstruiu um operador de alturas.

## B — O que foi demonstrado agora

Os novos nomes pertencem a `CarryTfvdJoint`, exceto os controles explicitamente em `CarryTfvdJoint.Control`.

### B.1 — Composição no produtor completo

Defina, **pela projeção do estado enriquecido original**, sem alterar seus campos:

- `value M z = T_M(z)`: valor da cabeça mais a cauda exata;
- `logJet M z = L_M(z)`: log-jet da cabeça mais sua cauda exata;
- `completionResponse z = B(z) = Xiᶜ(z)/Xi(z) + i Q'(s(z))/Q(s(z))`;
- `a(z) = originalResponse z = -F'(z)/F(z)`.

`full_response` reaproveita a identidade original

$$a(z)=B(z)+iL_M(z)/T_M(z).$$

A resposta é lida somente após o estado completo; os traços não são usados para definir retroativamente o carrier.

O numerador conjunto é

$$N_M(a,z)=T_M(a)T_M(z)[B(z)-B(a)]
 +i[T_M(a)L_M(z)-L_M(a)T_M(z)].$$

`jointNumerator_cocycle` e `numerator_transport` demonstram

$$\boxed{T_M(b)N_M(a,c)=T_M(c)N_M(a,b)+T_M(a)N_M(b,c).}$$

É uma identidade polinomial, válida inclusive quando o valor intermediário zera. Ela **não** autoriza dividir por esse zero, não diz que os determinantes sem pesos simplesmente somam e não prova que estados de câmeras distintas sejam iguais.

`numerator_eq_full_difference` prova, com os denominadores completos regulares,

$$N_M(a,z)=T_M(a)T_M(z)[a(z)-a(a)].$$

`readouts_cutoff_independent` e `numerator_cutoff_independent` demonstram a independência do cutoff para os readouts completados na seção física. Isso mantém as caudas exatas; não afirma a igualdade das cabeças ou a existência de uma isometria entre todos os estados enriquecidos.

### B.2 — Polarização física: o sinal do cruzamento importa

A forma física exige conjugação do primeiro argumento. Seu numerador é

$$\mathscr P_{M,P}(a,z)=\overline{T_M(a)}T_P(z)[B(z)-\overline{B(a)}]
 +i[\overline{T_M(a)}L_P(z)+\overline{L_M(a)}T_P(z)].$$

O **sinal mais** entre os dois cruzamentos logarítmicos é imposto por `conj i = -i`. Transportar ingenuamente o determinante não conjugado produziria o sinal errado.

`polarizedNumerator_quotient` demonstra

$$\mathscr P_{M,P}(a,z)=\overline{T_M(a)}T_P(z)[a(z)-\overline{a(a)}].$$

Cutoffs e pontos são independentes. Nenhuma parte Xi/chart foi descartada.

Sejam `K=k+1`, `z_j=i(j+1)/K` e `C_N(i,j)=1/(i+j+2)`, o Gram Cauchy **físico**. `basisSource` sintetiza o par completo original de um único coeficiente material; não é um vetor definido pelos momentos. `basisSource_pairing` e `radial_cauchy_denominator` fornecem

$$\Omega_{ij}=\frac{iK}{2}C_N(i,j)[\overline{a(z_i)}-a(z_j)],
\qquad (z_j-\overline{z_i})\frac{iK}{2}C_N(i,j)=-\frac12.$$

Portanto `physical_polarized_numerator` demonstra a identidade **multiplicada**

$$\boxed{2(z_j-\overline{z_i})\overline{T_M(z_i)}T_P(z_j)\Omega_{ij}
       =\mathscr P_{M,P}(z_i,z_j).}$$

`physical_basis_quotient` descarrega a divisão apenas na seção regular. `graph_pairing_sum` conserva todos os pares ordenados de dois inputs independentes.

### B.3 — Aplicação ao mesmo input crítico da PR #41

`fullSource_eventually_graph` identifica o vetor completo, uniformemente em todos os cutoffs exatos e inputs fixos. `fullSources_eventually_jointKernel` demonstra, antes da projeção real,

$$\Omega(\mathrm{fullSource}_M x,\mathrm{fullSource}_P y)
  =\sum_{i,j}\overline{v_k(x)_i}v_k(y)_j\,
    \frac{\mathscr P_{M,P}(z_i,z_j)}
    {2(z_j-\overline{z_i})\overline{T_M(z_i)}T_P(z_j)},$$

com `v_k = fixedMaterial`, a reconstrução de endpoint preexistente. Essa igualdade mantém as duas quadraturas e todos os cruzamentos; a métrica não é substituída por uma norma ajustada.

`critical_jointKernel_tendsto` aplica a expressão conjunta a `criticalCoordinates s n` e prova

$$\operatorname{Re}\sum_{i,j}\overline{v_{k,i}}v_{k,j}\,\mathrm{jointKernel}_{ij}
 \longrightarrow \mathrm{sourceMomentSchur}\ h\ s\ n.$$

A hipótese continua sendo somente `IsUnit (sourceMomentMatrix h s n)`. O cutoff pode ser qualquer schedule `M(k)` com caudas exatas. Os momentos escolhem uma combinação de teste; não definem o carrier físico nem uma métrica positiva.

### B.4 — Extração conjunta: primeiro termo e toda ordem

`value_hasDerivAt_zero` demonstra a regularidade do valor pelo teorema original da derivada material e seu log-jet completo. `full_response_zero` usa a paridade da característica para obter `a(0)=0`; nenhum valor central foi ajustado.

`centered_numerator_hasDerivAt` obtém diretamente

$$\boxed{\partial_z N_M(0,z)|_{z=0}=2T_M(0)^2h_0.}$$

O termo de derivada de T cancela porque multiplica a resposta **completa** no centro. `centered_numerator_coefficient` prova a confluência por `dslope` com a derivada verdadeira, em vez do fallback zero de um quociente singular.

Depois da síntese, `normalizedCenteredNumerator_eventuallyEq` e `centeredPolarizedReadout_eventuallyEq` identificam os germes normalizados com `a(z)`. Em particular, `centeredPolarizedReadout_odd_coefficient` prova, em toda ordem e para cutoffs independentes,

$$\frac{\partial_z^{2n+1}\{\mathscr P_{M,P}(0,z)/[\overline{T_M(0)}T_P(z)]\}|_{z=0}}{(2n+1)!}
 =2h_n.$$

É proveniência exata dos coeficientes, **não** uma representação Gram positiva. A identificação anterior dos coeficientes canônicos foi reutilizada; não se anuncia que a lei de sinais foi descoberta por extrair novamente h.

## C — O que foi refutado

Foi refutada a inferência específica:

> composição exata dos defeitos + paridade central + diagonal radial estritamente positiva bastam para tornar positiva a forma polarizada inteira.

O controle **auxiliar, não nativo**, é

$$F_\mathrm{test}(z)=\exp(-z^2-z^4/2-z^6/6),\qquad
 a_\mathrm{test}(z)=-F_\mathrm{test}'(z)/F_\mathrm{test}(z)=2z+2z^3+z^5.$$

`characteristic_ne_zero`, `characteristic_even` e `response_eq_logDerivative` certificam essas relações. `normalized_response` lê os coeficientes `1,1,1/2` da resposta dividida por 2. Não são momentos atribuídos à fonte Carry.

`radial_diagonal_pos` prova, para **todo y>0**,

$$\frac{\operatorname{Im}a_\mathrm{test}(iy)}{2y}
 =\frac{(y^2-1)^2+1}{2}>0.$$

A composição continua exata (`composition_still_holds`). Entretanto, com a métrica Cauchy e a síntese de duas pernas originais, em `K=10`,

$$v=(-51,100,-50,0),\qquad x=(-1,0,-1,0),$$

`material_endpoint` confirma o input fixo original; `full_original_form_negative` prova exatamente

$$\boxed{\operatorname{Re}\Omega(P(v,a_\mathrm{test}\odot v),P(v,a_\mathrm{test}\odot v))
       =-6199/20000<0.}$$

O residual do segundo bloco dos coeficientes do controle é `1/2-1²/1=-1/2`. Logo o problema está nos cruzamentos, mesmo com diagonais radiais positivas.

**Alcance:** esse controle não satisfaz por declaração toda a fonte aritmética C3/TFVD/Gamma de Carry. Ele exclui a dedução a partir das três propriedades citadas, não a possibilidade de uma lei adicional da fonte nativa. Nenhum pivô canônico negativo foi encontrado ou afirmado. Nenhum arquivo nativo foi modificado para produzir esse exemplo.

## D — O que permanece aberto e estado da validação

1. Não se demonstrou sinal novo do primeiro coeficiente sobrevivente em ordem crítica arbitrária. A fórmula exata do coeficiente e o limite ao pivô não dão seu sinal.
2. A identidade de composição é universal para quocientes dessa forma. Por isso, sozinha, não contém a restrição adicional da família aritmética original que o controle auxiliar não possui.
3. A independência de cutoff de um readout com caudas exatas não é uma isometria multibase, nem a reconstrução do estado por uma observação escalar. Não se anunciou independência de todos os caminhos de transporte.
4. A família positiva fiel e a calibração da primeira coluna dos gates do anexo continuam abertas. A identificação direta pelo clock material continua excluída no alcance da PR #36.
5. A continuidade/não anulação da cabeça da PR #65 não foi tomada como premissa; o produtor conjunto não divide pela cabeça. O no-go condicional específico da cabeça permanece com o mesmo alcance anterior.

Os módulos novos usam apenas os axiomas fundacionais permitidos (`propext`, `Classical.choice`, `Quot.sound`). O gerador enumera todas as definições e teoremas públicos e audita transitivamente **tipos e corpos**, com uma lista de dependências proibidas de positividade finita/posterior. Validação final: **17/17 checks passaram**, incluindo os sete módulos de pesquisa, builds focado e raiz com `--wfail`, as três auditorias e a regressão das doze fontes. São **41 teoremas e 13 definições**, totalizando **54 raízes públicas auditadas**. As cinco auditorias transitivas visitaram 4.867, 5.271, 5.521, 6.005 e 5.231 constantes, respectivamente; só os três axiomas fundacionais permitidos foram encontrados. As listas são fechamentos por grupo e não devem ser somadas como constantes distintas.

`experiment.py` reutiliza somente as funções de avaliação C3 da PR #65, sem executar seu código de topo, sem ler momentos para o produtor e sem reescrever arquivos antigos. Dois prefixos pequenos (J=64,128) testam composição, quociente, polarização e pareamento físico. O teste racional `Fraction` reproduz separadamente `-6199/20000`. A aproximação Taylor/EM continua sendo diagnóstico, não intervalo certificado, prova de sinal ou prova all-order.

Reprodução no host preparado:

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/tfvd-joint-response-transport
python3 research/tfvd-joint-response-transport/validate.py
```

O script compila explicitamente os módulos de pesquisa com `warningAsError`, executa builds focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/Analysis, regressão de doze fontes e controles de preservação. Os caches de módulos de pesquisa predecessores são explicitados em `compile_module.sh`; não se reivindica bootstrap de um clone vazio sem esses artefatos históricos. `evidence/checks.json`, logs e manifesto SHA-256 registram a execução.

## E — Próximo passo mínimo

A recomendação da PR #65 foi executada no nível de **identidade conjunta e extração de coeficientes**, com uma limitação clara: não surgiu uma desigualdade independente de sinal. Não basta seguir compondo a mesma identidade universal ou exigir que seu kernel seja positivo.

O próximo teste econômico deve ser específico da fonte C3 completada: tomar a primeira seção de **dois jets pares** do numerador polarizado acima e fazer a somação TFVD conjuntamente, antes de separar cabeça e cauda. O alvo escalar de verificação é

$$b_1b_5-b_3^2=4(h_0h_2-h_1^2),\qquad
 b_r=a^{(r)}(0)/r!.$$

Essa desigualdade escrita isoladamente é equivalente ao sinal finito procurado; **não é oferecida como hipótese estrutural nova**. A obrigação realmente nova seria uma identidade de fluxo/somação por partes do lado esquerdo nos canais C3 originais que exponha seus termos de bordo e um resto controlável, com sinal derivado da própria fonte. O controle auxiliar mostra por que tal identidade precisa usar mais do que paridade, composição ou positividade diagonal.

Começar nessa seção permite refutar rapidamente uma proposta errada e comparar com o caso finito já certificado, sem usar esse certificado como causa da nova prova. Se nenhum termo da fonte fornecer a orientação necessária, registrar a obstrução específica. Somente depois de uma identidade efetiva nessa seção faz sentido tentar a generalização para as direções de ordem maior.

**Conclusão:** a pista do anexo fornece uma composição exata útil e agora ligada ao pareamento completo e aos mesmos momentos. Ainda não fornece a causa do sinal. A fonte, suas correções e os cruzamentos foram preservados; a classificação permanece `PARTIAL`.
