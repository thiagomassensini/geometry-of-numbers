# Teste do crescimento radial como mecanismo independente de sinal

Classificação: **PARTIAL para a obrigação de sinal da #125; NO-GO específico para a positividade do kernel gerador investigado.** Não é um NO-GO da geometria Carry, da fonte original ou da positividade canônica all-order.

Base: PR #125, commit `83d035b5714c2cbadcd7f24bb50dd507b1fafe30`, branch `agent/native-moving-euler-balance`. Nova branch independente: `agent/native-radial-flow-audit`. A #125 foi conferida aberta, draft e sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Execução no host `llm`.

## A — O que já estava demonstrado

1. A #125 identifica o limite do balanço dos canais originais, para ordem finita fixada e cartas Euler convergentes, com `nativeSourceFiniteBoundaryEnergy`. Seu `physical_green_pairing_euler_tendsto` conserva também os pareamentos polarizados. Esses limites não fornecem o sinal.
2. A #41 separa ortogonalização algébrica de positividade: `sourceMomentSchur_sewing_of_isUnit` e `sourceMomentSchur_critical_direction_of_isUnit` exigem a inversibilidade do bloco antigo, sem impor seu sinal nessa etapa algébrica. Consultamos a branch histórica; não a modificamos nem a integramos. A presente prova não recebe um whitening ou um pivô positivo.
3. `completedNativeHermiteBiehlerChiralQuotient` é o quociente dos dois canais Hermite–Biehler originais. `completedNativeChiralPickFactorization_eventually_regular` fornece a regularidade local necessária. O quociente vale −1 no centro.
4. `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` e seu análogo par identificam todos os coeficientes da mesma resposta com os momentos canônicos. `nativeSourceLogSlope_analyticAt` fornece o germe analítico.
5. `material_theta_integral_input` e `mem_logMomentBox`, dos certificados históricos de integrais, fornecem caixas racionais estreitas para os momentos originais. Reutilizamos essas inclusões, **sem utilizar os teoremas posteriores de positividade dos pivôs**.

O candidato testado foi uma lei mais forte que a positividade final: crescimento de Loewner do defeito do retorno ao afastar a grade radial do centro. Se existisse, permitiria tentar integrar uma forma derivada positiva. Era necessário testar seus cruzamentos antes de adotá-la como mecanismo.

## B — O que foi demonstrado agora

### B.1 — Gerador proveniente do quociente original

Sejam F a característica completada original e Q=−F′/F. Em [SourceJets.lean](SourceJets.lean) e [CayleyFlow.lean](CayleyFlow.lean) provamos:

$$q(z)=\frac{Q(z)-i}{Q(z)+i},\qquad
\mathcal R(z)=\frac{zQ'(z)}{1+Q(z)^2},\qquad
\boxed{zq'(z)=2i\mathcal R(z)q(z)}.$$

As igualdades do quociente e da derivada são locais no centro, com a regularidade descarregada pela fonte existente. Os nomes são `original_quotient_eq_cayley`, `original_quotient_analytic` e `original_quotient_flow_equation`.

R é um **diagnóstico derivado da fonte**, não outra sequência canônica, nova métrica ou novo operador de alturas. Não introduzimos zeros ou alturas como entradas.

`source_tc_odd` e `source_tc_even` conferem os fatores 2 e os fatoriais: se a=2h₀, b=2h₁, c=2h₂, d=2h₃, então Q(z)=az+bz³+cz⁵+dz⁷+… . `flow_tc_recurrence` deriva os coeficientes de R da identidade exata R+Q²R=zQ′.

### B.2 — Coeficientes efetivos e testemunha racional negativa

[FlowJets.lean](FlowJets.lean), teorema `flow_first_eight`, determina os primeiros oito coeficientes de Taylor de R. Os pares são zero e os quatro ímpares são:

$$\begin{aligned}
\mu_0&=a,\\
\mu_1&=3b-a^3,\\
\mu_2&=5c-5a^2b+a^5,\\
\mu_3&=7d-7a^2c-7ab^2+7a^4b-a^7.
\end{aligned}$$

A testemunha fixa é u=7/1000. [FlowInterval.lean](FlowInterval.lean) certifica, com aritmética inteira reduzida pelo kernel e as inclusões integrais antigas:

$$\boxed{W=u^2\mu_1-2u\mu_2+\mu_3<0}.$$

`source_flow_witness_neg` é a desigualdade dos quatro momentos originais; `actual_flow_jet_witness_neg` identifica a mesma combinação com os coeficientes da função R efetiva. Não se assume o sinal de nenhuma Hankel. Numericamente W≈−8,20294944×10⁻¹⁰, mas esse decimal não é uma premissa Lean.

A forma de jets deslocada [[μ₁,−μ₂],[−μ₂,μ₃]] tem, portanto, uma direção negativa (u,1). O sinal é de um gerador derivado, **não dos momentos canônicos h**.

### B.3 — Quatro endereços, todos os cruzamentos e a cauda analítica

Em [KernelTaylor.lean](KernelTaylor.lean), use d=(1,2,3,4), h complexo perto de zero e

$$w(h)=(-1,3,-3,1)+6u h^2(-1,1,0,0).$$

`fourFlowKernel` é a soma completa:

$$\Psi(h)=\sum_{r,s<4}w_r(h)w_s(h)
\frac{-i[\mathcal R(id_rh)+\mathcal R(id_sh)]}{d_r+d_s}.$$

Para h real, os coeficientes w são reais. Esta definição é a extensão analítica de um teste bilinear real; não se declara que seja uma forma hermitiana para h complexo arbitrário.

`fourFlowKernel_reduction` soma as **16 interações** antes de reduzir a quatro avaliações escalares. `fourFlowKernel_exact_remainder` prova, para uma função A analítica no centro:

$$\boxed{\Psi(h)=36Wh^7+h^8 A(h)}.$$

O resto inclui toda a fonte superior; não foi substituído por zero nem estimado a partir do checkpoint. `fourFlowKernel_normalized_tendsto` demonstra Ψ(h_k)/h_k⁷→36W, para o passo nativo h_k=1/(k+1).

[KernelSign.lean](KernelSign.lean) conclui `fourFlowKernel_eventually_neg` e `fourFlowMatrix_eventually_not_nonnegative`: o kernel real completo de R possui uma direção negativa em toda grade nativa suficientemente fina. `fourFlowKernel_real_form` confere a igualdade com a soma quadrática real, não somente com entradas diagonais.

### B.4 — Derivada do defeito em dois endereços independentes

[RadialDefect.lean](RadialDefect.lean) mantém q_r(h)=q(id_rh) e define apenas o readout analítico

$$D_{rs}(h)=\frac{1-q_r(h)q_s(h)}{d_r+d_s}.$$

`radial_defect_flow` prova, para cada par r,s e h perto do centro:

$$\boxed{hD'_{rs}(h)=2q_r(h)q_s(h)
\frac{-i[\mathcal R(id_rh)+\mathcal R(id_sh)]}{d_r+d_s}}.$$

Ambos os fatores do retorno são diferenciados. O denominador Cauchy permanece. O teorema é complexo e não postula que D seja automaticamente a energia física: a realidade radial é provada separadamente, mas o domínio físico e o transporte vetorial ainda exigem a identificação indicada abaixo.

### B.5 — Realidade radial derivada da reflexão nativa

[RadialReality.lean](RadialReality.lean) reutiliza `response_real_ray`, já provado em `ResponseReality.lean` a partir da reflexão do canal nativo completado. `original_rotated_response` confere Q(iz)=2i responseReadout(z); `original_quotient_radial_real` demonstra conj(q(it))=q(it) para t real suficientemente perto do centro. Essa realidade não é recebida como hipótese de positividade. Assim, a restrição real do D acima é de fato o defeito com conjugação do mesmo quociente. Ainda falta identificá-lo com a família vetorial física e seus fatores de amplitude.

## C — O que foi refutado e o alcance da obstrução

Foi refutada a proposta de que o kernel gerador R seja não negativo em todas as direções reais, mesmo em quatro endereços arbitrariamente próximos do centro. A cauda não restaura esse sinal: a fatoração com resto analítico fornece a negatividade eventual do kernel efetivo.

Isso exclui usar **essa positividade do gerador** como premissa universal independente para provar o sinal canônico. Não foi refutada a positividade dos balanços acumulados, dos pivôs canônicos ou da fonte completa. Uma forma acumulada positiva pode ter derivada negativa em uma direção.

Não anunciamos ainda um NO-GO formal da monotonicidade das energias físicas: `radial_defect_flow` é uma identidade do readout analítico do quociente. O transporte desse readout à família física de incidência fixa ainda precisa preservar a amplitude e o domínio originais. Confundir essas duas etapas repetiria precisamente a inversão de proveniência que a investigação deve evitar.

Os certificados anteriores de H6/K6 e as realizações físicas finitas não são contraditos nem usados como premissas aqui. A #41 permanece relevante: ortogonalização algébrica e interpretação como norma positiva continuam sendo afirmações distintas.

O script [mechanism_probe.py](mechanism_probe.py) verifica 64 contribuições racionais do stencil, além de quatro testes decimais com todos os cruzamentos. Os testes usam somente `canonical_h` do checkpoint histórico, sem recalcular momentos. São diagnósticos de um prefixo de Taylor sem cota de cauda e não certificados da função infinita. A prova Lean, ao contrário, usa a resposta analítica original e seu resto completo.

## D — O que permanece aberto

1. O sinal de `nativeSourceFiniteBoundaryEnergy` em toda ordem continua aberto. W<0 não é um pivô canônico negativo.
2. A identificação do D analítico com a diferença de normas no **mesmo estado incidente físico fixo** não foi formalizada nesta etapa. Ela precisa incluir conjugação, domínio, as duas pernas e o fator original sqrt(k+1) das features radiais. Mudar k mantendo os mesmos coeficientes não mantém automaticamente o mesmo estado físico.
3. A identidade B.4 não elimina o termo de transporte de uma direção móvel. Se os coeficientes forem v(h), a derivada da forma completa também contém os cruzamentos com v′(h).
4. Não há uniformidade na ordem, operador infinito, positividade de espectro ou novas alturas certificadas nesta entrega. Também não se postula uma transformação unitária entre estados geométricos e theta.

As definições e identidades publicadas são verificadas no kernel; as aproximações decimais são identificadas como diagnósticos. As etapas físicas listadas acima são obrigações abertas, não campos de uma estrutura recebida como hipótese.

## E — Próximo passo mínimo e reprodução

A tentativa de tornar cada derivada radial não negativa é forte demais para o gerador testado. A próxima obrigação de sinal deve tratar o **balanço completo acumulado na trajetória crítica original**, sem descartar o transporte dos coeficientes.

O próximo teorema técnico concreto é identificar, para a carta Euler/Newton física já construída nas #124–#125, a derivada da forma completa com

$$\frac{d}{dh}\big(v(h)^*D(h)v(h)\big)
=v(h)^*D'(h)v(h)+2\operatorname{Re}\big(v'(h)^*D(h)v(h)\big),$$

com os fatores de amplitude físicos efetivos, os bordos e os canais originais. A identidade acima descreve o alvo; **não foi formalizada para essa trajetória física nesta entrega**. Antes de tentar seu sinal all-order, testar a primeira direção crítica não trivial sem apagar o segundo termo. Uma estimativa do conjunto precisa vir da fonte e não receber o pivô positivo ou uma contração equivalente como hipótese. O contraexemplo de R é um teste obrigatório de qualquer proposta que tente eliminar esse termo ou impor positividade termo a termo.

No host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

O primeiro comando restaura opcionalmente os 114 objetos da #125, verificando fontes, objetos, toolchain, manifesto e pins. SHA256 do cache de entrada: `0ac55dc79a44b81c639971f9aebae2b781bc28e3bf7b52fdd5d4bc5bef800853`. `build_extra.py` recompila os 48 ancestrais históricos das caixas integrais, sem nova quadratura ou novos momentos. Após essa compilação, `--reuse-extra` verifica seus hashes em vez de repeti-la. Sem cache, `python3 validate.py` recompila todos os ancestrais.

Checkpoint diagnóstico: `native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv`, coluna `canonical_h`, SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`. O checkpoint não participa das provas Lean.

### Validação concluída

**22 checks passaram**, todos com exit 0. São **33 teoremas e 20 definições públicas**, em oito módulos matemáticos novos, além do módulo Audit gerado. As compilações individuais usam warnings como erros. Passaram os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis.

Foram reutilizados e verificados 114 objetos ancestrais da #125, sem anunciá-los como recompilados. Os 48 ancestrais das caixas integrais foram recompilados a partir das fontes históricas exatas nesta execução; a validação final voltou a conferir seus hashes. As 64 contribuições racionais do stencil e os quatro testes decimais passaram.

As 53 raízes públicas possuem `#print axioms` e auditoria transitiva de tipos e corpos, incluindo opacos com `value? (allowOpaque := true)`. O grupo algébrico tem 11 raízes e 27245 dependências; o grupo da fonte, 27 e 57235; o grupo de certificação, 15 e 58278. Os certificados finitos de positividade canônica enumerados e as equivalências de positividade indicadas estão proibidos na auditoria. A certificação exige a presença efetiva das inclusões integrais, da identificação dos jets da fonte e do resto analítico completo. Só são aceitos os axiomas fundacionais `propext`, `Classical.choice`, `Quot.sound`.

Não há `sorry`, `admit`, `native_decide` ou novos axiomas. Fontes, pesos, métricas, amplitudes, dressing, completion, pins e trabalhos antigos foram preservados. As evidências estão em `evidence/validation.json`, `evidence/kernel-audit-summary.json`, `evidence/extra-upstream-build.log`, `evidence/extra-upstream.json` e `evidence/preservation.json`; `SHA256SUMS` registra os arquivos da entrega. Validação observada no host `llm`, sem reivindicação de CI externo.

A publicação usa PR draft empilhada sobre a #125, sem merge automático. Fontes e cache verificados são arquivados localmente antes da remoção somente do worktree próprio; a branch e todos os trabalhos anteriores são preservados.

Fim do relatório — gerador radial testado na fonte original, obstrução específica identificada, proveniência física restante e obrigação canônica de sinal explicitadas.
