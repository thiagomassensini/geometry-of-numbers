# Fatoração geométrica de U₁ e o bordo necessário à extensão

**Resultado: PARTIAL para a positividade Hankel em toda ordem; alvo U₁ fechado.**
A fatoração candidata da PR #95 foi demonstrada no espaço físico original e
fornece uma cota estrita, sem sinais canônicos como premissa. Uma comparação
com a quarta diferença também conserva um defeito de bordo não nulo.

Base: `31a5315801742946b2e293b1cbfa83f58df3b7d5`, head da PR #95,
branch `agent/native-critical-tfvd-cancellation`. A nova branch é
`agent/native-curvature-green-factor`, destinada à PR #95, sem merge automático.
O operador consultado permanece em `bfeb10fd2425400fa38139903d12bf0599f02e53`;
main, em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

O espaço é o carrier Cauchy original `Lp ℂ 2 volume` no intervalo unitário,
com suas colunas físicas `φ_j(u)=sqrt(u) u^j`. Não se troca seu produto interno.
`physicalRadialAdvance`, de `NativeIntervalMultiplier.lean`, é a multiplicação
por u. `NativePhysicalGreenResolvent.lean` fornece, para `0<η<1`,

\[
M=M_u,\quad R_\eta=(I-\eta M)^{-1},\quad
G_\eta=\eta M R_\eta^2.
\]

As inversas, a autoadjunção, as identidades de multiplicadores e o avanço
`M φ_j=φ_{j+1}` já existiam. A PR #93 transportou a TFVD com os dois traços;
a PR #94 identificou o comutador comum das duas amplitudes quirais.

A PR #95 resolveu os setores originais na direção `J₂−aJ₀`, com a livre:

\[
\begin{aligned}
Z_k&=s^4 A_4+s^2 A_2+A_0+t^2E_C(t),\\
B_k&=-s^4 A_4-s^2 A_2+F(a)-A_0+t^2(E_Q(t)-E_C(t)),\\
Q_k&=B_k+Z_k\longrightarrow F(a)=h_2-2ah_1+a^2h_0,
\end{aligned}
\]

onde `s=k+1`, `t=1/s`. Z é o misto completo do comutador; B é o pareamento
assinado de Green + bordo. Não são normas isoladas. `A₄=2h₀U₁` e

\[
U_1=\Re\langle Sd,G_\eta S(C_\eta[p_1]d)\rangle,
\quad d=(-1/2,1,-1/2),\quad p_1(j)=j+1.
\]

S é a síntese existente. O endereço de saída 3 e todos os cruzamentos já
estavam nessa definição. O índice radial não é profundidade Carry.

## B — O que foi demonstrado agora

### B.1 — Contratividade no mesmo espaço físico

`ComplementNorm.lean` prova

\[
\|I-qM\|\le1\quad(0\le q\le1),\qquad
\|Cf\|\le\|f\|\quad(C=I-M).
\]

`physical_valve_norm_le_one` usa o multiplicador original `1-qu`, sem mudar
métrica, domínio ou pesos. `physical_complement_contracts` é sua especialização.
Da inversa física já provada segue `resolvent_norm_lower`:

\[
\|f\|\le\|R_\eta f\|.
\]

Todos esses operadores são limitados no carrier inteiro. Não há passagem
silenciosa por um domínio de clock não limitado.

### B.2 — Fatoração polarizada, antes da leitura diagonal

Para expor a identidade operatorial, ponha

\[
d_f=-\tfrac12 C^2f,\qquad
t_f=-\frac1{2\eta}Mf-\eta M d_f,\qquad
v_f=R_\eta MCf.
\]

São expressões nos operadores físicos anteriores. A parcela `Mf/(2η)` é
mantida: ela carrega a contribuição de bordo desta identidade.

`curvature_green_polarized_factor`, em `CurvatureKernel.lean`, prova para duas
entradas independentes f e g:

\[
\boxed{
\langle d_f,G_\eta t_g\rangle
=\tfrac14\left(\langle v_f,v_g\rangle
              -\eta^2\langle Cv_f,Cv_g\rangle\right).
}
\]

A prova transporta ambos os argumentos pela autoadjunção de M e R e usa sua
comutação. Não parte de igualdade entre normas diagonais. Depois, a
contratividade de C fornece `curvature_green_lower_bound`:

\[
\boxed{
\Re\langle d_f,G_\eta t_f\rangle
\ge\frac{1-\eta^2}{4}\|v_f\|^2\ge0.
}
\]

Esse é um teorema geral de operadores. Sua identificação com um comutador
nativo exige verificar as duas entradas. Não se declara que todos os stencils
nativos sejam obtidos simplesmente repetindo C; o teste em C abaixo mostra
um defeito preciso nessa extrapolação.

### B.3 — Identificação efetiva com U₁ e cota estrita

`NativeCoefficient.lean` prova antes do pareamento:

\[
d_{\phi_0}=Sd,\qquad
t_{\phi_0}=S(C_\eta[p_1]d),\qquad
v_{\phi_0}=R_\eta(\phi_1-\phi_2).
\]

São `native_curvature`, `native_tangent` e `native_transported_gradient`.
Isso identifica o objeto da PR #95, em vez de substituí-lo por um kernel
positivo auxiliar. `native_u1_factor` fecha exatamente a candidata:

\[
\boxed{U_1=\tfrac14(\|v\|^2-\eta^2\|Cv\|^2)},
\quad v=R_\eta(\phi_1-\phi_2).
\]

Da Gram original das colunas, sem momentos canônicos, calcula-se

\[
\|\phi_1-\phi_2\|^2=\tfrac14-\tfrac25+\tfrac16=\tfrac1{60}.
\]

Com a cota do resolvente e a contratividade de C, `native_u1_lower_bound` e
`native_u1_pos` dão

\[
\boxed{U_1\ge\frac{1-\eta^2}{240}>0\quad(0<\eta<1).}
\]

240 é `4×60`, determinado pela fatoração e pela Gram física existente.
Não é uma constante ajustada nem uma nova normalização. Nenhum sinal de h₀,
de pivô ou de Hankel entra nessa demonstração.

### B.4 — Consequências para os setores da mesma fonte

`CriticalSectorSign.lean` primeiro prova, sem receber sinal de momento,

\[
Z_k/s^4\to A_4,\qquad B_k/s^4\to-A_4.
\]

Somente nos quatro corolários de sinal se reutiliza o resultado preexistente
`canonicalCompletedNativeLogDerivativeMoment_zero_pos`. Então

\[
A_4=2h_0U_1\ge h_0\frac{1-\eta^2}{120}>0.
\]

`mixed_eventually_positive` e `bulk_boundary_eventually_negative` concluem,
para cada a fixo, que Z fica positivo e B negativo eventualmente. O termo
quártico potencial da PR #95 é, portanto, efetivo. A soma Q continua tendo o
limite finito anterior; não se ignora a compensação entre os setores.

O uso de h₀>0 nesses corolários vem do certificado anterior da fonte theta.
O nome é reutilizado de `CompletedC3FullWronskianCentralChiralEnergy.lean`.
Esta rodada não o reprova por geometria. A fatoração e a cota estrita de U₁
são independentes desse certificado, da sequência canônica e da característica
completada, como verifica a auditoria separada.

## C — O que foi refutado na extensão direta

`FourthBoundaryDefect.lean` usa literalmente os pesos existentes da quarta
diferença divididos por `4!`, sem o fator radial:

\[
d_4=(1,-4,6,-4,1)/24.
\]

O seed candidato `f₄=−C²φ₀/12` reproduz a curvatura:
`physicalCurvature f₄=S d₄`. Mas não reproduz o comutador nativo. A identidade
exata `fourth_tangent_defect` é

\[
\boxed{
S(C_\eta[p_1]d_4)
=t_{f_4}+\eta^{-1}
 \left(\tfrac5{24}\phi_1-\tfrac1{12}\phi_2\right).
}
\]

`fourth_commutator` conserva todas as saídas até o endereço 5.
`fourth_tangent_not_direct_lift` prova que o defeito não é zero para η>0.
O teste não consiste em comparar apenas um escalar ou uma norma: a curvatura
coincide como vetor e a segunda entrada falha por um vetor explícito.

Isso refuta a identificação específica do comutador da quarta diferença com
a repetição direta da fórmula quadrática. Não refuta positividade em quarta
ordem, nem uma extensão corrigida por esse bordo, nem a geometria original.
Não se atribui um sinal ao pareamento adicional sem uma demonstração própria.

A PR #94 tinha misto eventualmente negativo no primeiro jet. O sinal positivo
agora provado vale em J₂−aJ₀. Não existe autorização para extrapolar um desses
comportamentos a todos os jets.

## D — Alcance, dependências e validação

O alvo U₁ está fechado por uma identidade geométrica e por uma cota estrita.
A identidade operatorial polarizada vale para todos f e g no espaço original;
a costura nativa demonstrada é a do stencil quadrático. A comparação com a
quarta diferença registra o bordo necessário em vez de apagá-lo.

Não se demonstrou uma Gram positiva igual à Hankel canônica em toda ordem.
Uma lei de sinal do coeficiente dominante não determina o sinal da parte
finita que resta depois de seu cancelamento. Em particular, a positividade de
U₁ não substitui a obrigação de sinal do Schur da PR #41.
Sua cota não é uma margem uniforme dos pivôs em ordens crescentes. Também não
se pressupõe que S seja uma isometria da torre vertical ou que sua Gram bruta
seja a identidade.

A dependência em η pertence aos setores dessa decomposição. Não é uma
transformação dos momentos ou uma mudança de câmera destinada a torná-los
positivos. Fonte, duas pernas, amplitudes, métrica, cruzamentos e completamento
permanecem os mesmos. A síntese e o Green mantêm a cauda física completa.

`Audit.lean` percorre transitivamente tipos e corpos e imprime os axiomas de
todas as raízes públicas. O grupo espacial rejeita dependências da sequência
canônica e da característica completada. A identificação assintótica permite
os coeficientes canônicos, mas rejeita seus certificados de sinal. Só o grupo
de quatro corolários admite explicitamente o h₀>0 anterior. Axiomas permitidos:
`propext`, `Classical.choice`, `Quot.sound`. Sem `sorry`, `admit`,
`native_decide` ou axiomas matemáticos novos.

São 39 teoremas, sete definições e duas abreviações públicos, em cinco módulos.

| Grupo auditado | Raízes públicas | Dependências transitivas de tipos/corpos |
| --- | ---: | ---: |
| Geometria espacial, sem momentos nem característica completada | 41 | 5.486 |
| Coeficientes e limites, sem certificados de sinal | 3 | 5.693 |
| Corolários que reutilizam h₀>0 | 4 | 5.693 |

Os conjuntos se sobrepõem; os totais transitivos não devem ser somados.

`validate.py` recompila os dezenove ancestrais realmente importados e verifica
seus hashes contra a base; compila todos os módulos novos e Audit com warnings
como erros; executa `lake build --wfail`, as auditorias Foundation, Geometry e
Analysis e as verificações de preservação. Os comandos e os resultados ficam
em `evidence/validation.json`; fontes, pins e trabalho antigo protegido, em
`source-provenance.json` e `preservation.json`. A raiz Lake não inclui estes
módulos de pesquisa automaticamente, por isso são compilados explicitamente.
Nesta execução, **os 16 comandos passaram com código de saída zero**, assim
como as verificações finais de preservação das fontes, dos pins e dos trabalhos
antigos. `MANIFEST.sha256` permite conferir os arquivos entregues com
`sha256sum -c MANIFEST.sha256` nesta pasta.

## E — Próxima obrigação mínima

A próxima comparação de quarta ordem já tem o termo que precisa conservar.
O primeiro lema concreto a tentar é o sinal do pareamento físico

\[
\Re\langle S d_4,G_\eta
 (\tfrac5{24}\phi_1-\tfrac1{12}\phi_2)\rangle,
\]

com o mesmo Green e as mesmas colunas. Só depois se pode combinar esse termo
com a fatoração e testar uma lei para os bordos dos stencils de maior ordem.
Esse alvo testa o alcance da lei espacial; não deve virar uma campanha de
sinais dominantes apresentada como solução dos residuais finitos.

A obrigação principal all-order permanece uma identidade ou desigualdade da
fonte completada que determine o sinal da soma finita completa, após todos os
cancelamentos. A nova norma controlada resolve um componente real dessa cadeia;
não recebe a positividade Hankel por outro nome.

Reprodução no servidor `llm`, na pasta desta investigação:

```bash
python3 validate.py
```

Entrega em PR draft sobre a PR #95, sem merge automático. Main, pins e os
trabalhos anteriores são preservados.

**Fim do relatório.**
