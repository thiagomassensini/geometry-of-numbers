# Sinal do bordo quártico no Green nativo

**Classificação: PARTIAL para a positividade Hankel all-order; alvo do bordo
quártico fechado.** O cruzamento da PR #96 tem sinal positivo e uma cota
geométrica explícita. Conservando esse termo, o coeficiente espacial completo
da quarta diferença também recebe uma cota positiva. Uma identidade escalar
dos polinômios de bordo foi demonstrada em ordem arbitrária; sua calibração
operatorial com todos os stencils nativos permanece uma obrigação separada.

Base: `c585b8267dcd31eb810256ac94212403f1e0fd7a`, head da PR #96,
branch `agent/native-curvature-green-factor`. Esta continuação está em
`agent/native-quartic-boundary-sign`, destinada à PR #96, sem merge automático.
O operador permanece em `bfeb10fd2425400fa38139903d12bf0599f02e53` e main em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

Usamos o espaço Cauchy físico original, com
`φ_j(u)=sqrt(u) u^j`, a síntese S e os operadores existentes

\[
M=M_u,\quad C=I-M,\quad R_\eta=(I-\eta M)^{-1},\quad
G_\eta=\eta M R_\eta^2,\qquad 0<\eta<1.
\]

As PRs #93–#95 mantiveram as duas pernas, os dois traços e todos os
cruzamentos na síntese completada antes de extrair os coeficientes espaciais.
A PR #96 demonstrou a contratividade de C e a expansão inversa
`‖f‖≤‖Rη f‖`, no mesmo domínio físico.

Para `d_f=−C²f/2`, `t_f=−Mf/(2η)−ηMd_f` e `v_f=RηMCf`, ela já provou a
fatoração polarizada e o controle diagonal

\[
\Re\langle d_f,G_\eta t_f\rangle
=\tfrac14(\|v_f\|^2-\eta^2\|Cv_f\|^2)\ge0.
\]

Essa identidade não basta para identificar o comutador de qualquer nova ordem.
O resultado `fourth_tangent_defect` da PR #96 conserva o defeito nativo exato:

\[
d_4=(1,-4,6,-4,1)/24,\quad f_4=-C^2\phi_0/12,\quad
b_4=\tfrac5{24}\phi_1-\tfrac1{12}\phi_2,
\]

\[
Sd_4=d_{f_4},\qquad
S(C_\eta[p_1]d_4)=t_{f_4}+\eta^{-1}b_4,\qquad p_1(j)=j+1.
\]

Os pesos de d₄ são os da quarta diferença original divididos por `4!`.
O termo no endereço 5 permanece no comutador. A fonte, a métrica e os pesos
não foram substituídos nesta continuação.

## B — O que foi demonstrado agora

### B.1 — Fatoração do bordo em dois argumentos

Para duas entradas físicas independentes f e g, defina somente as expressões
nos operadores anteriores

\[
q_f=C^4f/24,\qquad b_f=M(5f-2Mf)/24,\qquad
w_f=R_\eta MC^2f.
\]

`quartic_boundary_polarized_factor`, em `BoundaryFactor.lean`, demonstra

\[
\boxed{
\langle q_f,G_\eta b_g\rangle
=\frac\eta{576}\left(5\langle w_f,w_g\rangle
                       -2\langle w_f,Mw_g\rangle\right).
}
\]

A prova usa autoadjunção e comutação dos mesmos multiplicadores e do
resolvente. O pareamento misto com M é conservado. A especialização diagonal
só acontece depois da identidade polarizada.

Como M é contrativo no carrier original,

\[
\Re\langle w,Mw\rangle\le\|w\|^2,
\qquad
\Re\langle q_f,G_\eta b_f\rangle\ge\frac\eta{192}\|w_f\|^2.
\]

São `advance_inner_upper` e `quartic_boundary_lower`. O fator espacial é
`5I−2M=3I+2C`; a cota três vem desse operador, não de uma margem de Hankel.

### B.2 — Identificação com o bordo nativo e sinal estrito

`QuarticCoefficient.lean` prova as identidades vetoriais

\[
q_{\phi_0}=Sd_4,\quad b_{\phi_0}=b_4,\quad
w=w_{\phi_0}=R_\eta(\phi_1-2\phi_2+\phi_3).
\]

São `native_quartic_vector`, `native_boundary_vector` e
`native_quartic_gradient`. A partir da Gram Cauchy já existente,

\[
\|\phi_1-2\phi_2+\phi_3\|^2=\frac1{280}.
\]

A desigualdade do resolvente fornece `‖w‖²≥1/280`. Portanto,
`native_boundary_pair_lower` e `native_boundary_pair_pos` provam

\[
\boxed{
\mathcal B_4:=\Re\langle Sd_4,G_\eta b_4\rangle
\ge\frac\eta{53760}>0.
}
\]

53760 é `192×280`, deduzido dos coeficientes anteriores e da norma na métrica
original. Não é um ajuste de normalização. Nenhum sinal de momento canônico,
pivô ou matriz Hankel entra nessa prova.

### B.3 — O coeficiente completo, conservando o defeito

Defina a leitura do comutador nativo inteiro

\[
\mathcal U^{[4]}_\eta
=\Re\langle Sd_4,G_\eta S(C_\eta[p_1]d_4)\rangle.
\]

`native_quartic_coefficient_split` usa literalmente o defeito da PR #96:

\[
\mathcal U^{[4]}_\eta
=\Re\langle d_{f_4},G_\eta t_{f_4}\rangle+\eta^{-1}\mathcal B_4.
\]

A primeira parcela tem o controle de normas anterior; a segunda acaba de ser
certificada com seus coeficientes originais. Juntas dão

\[
\boxed{\mathcal U^{[4]}_\eta\ge\frac1{53760}>0.}
\]

São `native_quartic_coefficient_lower` e `native_quartic_coefficient_pos`.
Também se provou a identidade completa `native_quartic_coefficient_factor`:

\[
\boxed{
\mathcal U^{[4]}_\eta=\frac1{576}\left(
5\|w\|^2-2\Re\langle w,Mw\rangle
+\|Cw\|^2-\eta^2\|C^2w\|^2\right).
}
\]

O cruzamento com M e o termo assinado `−η²‖C²w‖²` permanecem. O controle vem
de suas relações com as outras parcelas, sem trocar a fonte por uma norma.

Essa U é um coeficiente **espacial da resposta linear** no stencil quártico.
Os momentos canônicos e os pivôs de Schur mantêm suas definições anteriores.
Uma cota desse coeficiente não fornece uma margem dos residuais finitos após
todos os cancelamentos da fonte completada.

### B.4 — Identidade algébrica em ordem arbitrária

`BoundaryPolynomial.lean` introduz a leitura escalar recursiva do candidato a
bordo geral:

\[
P_0(x)=0,\qquad P_{n+1}(x)=n+2+xP_n(x).
\]

O índice n corresponde à ordem da diferença menos dois. Não é profundidade
Carry, endereço material ou índice de momento. Os teoremas provam, para todo n,

\[
\boxed{(1-x)^2P_n(x)=n+1-(n+2)x-x^n+2x^{n+1}},
\]

\[
P_n(x)\ge0\ (x\ge0),\qquad P_{n+1}(x)\ge n+2\ (x\ge0).
\]

Na coordenada física `x=1-u`, a mesma identidade é

\[
\boxed{
u^2P_n(1-u)=(1-u)^n(1-2u)-1+(n+2)u.
}
\]

Em particular, `P₂(x)=3+2x`, que reproduz exatamente o fator `5−2u` do bordo
quártico. São `boundary_polynomial_identity`, `boundary_polynomial_lower`,
`boundary_polynomial_in_native_coordinate` e `boundary_polynomial_two`.

Os polinômios não definem outra sequência de momentos ou uma nova fonte.
São uma identidade finita de diferenças e de bordo, com positividade escalar
demonstrada. A identificação operatorial com todos os comutadores nativos
ainda precisa ser provada; ela não é recebida como hipótese de positividade.

## C — O que foi refutado ou esclarecido

O NO-GO específico da PR #96 continua válido: a extensão direta de `t_f` não
é o comutador quártico nativo. A presente prova conserva a diferença e determina
seu pareamento; a contribuição do bordo é positiva nesse stencil.

Consequentemente, descartar o defeito apagaria uma contribuição estritamente
positiva e modificaria o coeficiente. Não se contorna a obstrução alterando
o lift, a fonte ou a métrica. Usa-se a identidade original com a correção inteira.

A coincidência de `P₂(1-u)` com o bordo quártico não prova sozinha uma
representação nativa em todas as ordens. Tampouco o sinal de coeficientes
dominantes prova o sinal da parte finita do balanço. Os certificados anteriores
de positividade finita permanecem intactos.

## D — Alcance e auditoria

O alvo pedido foi fechado com identidades vetoriais, uma fatoração polarizada e
cotas estritas do próprio pareamento. Todos os resultados novos são espaciais:
não dependem da sequência canônica, da característica completada ou de seus
certificados de sinal. As relações com os setores da fonte completada são as
já provadas nas PRs anteriores; não se proclama uma Gram Hankel nova.

O Green é o resolvente original, no carrier completo. Não houve corte de cauda
física, normalização de vetores, troca de câmera ou identificação da síntese
com uma isometria. A ordem dos operadores e todos os termos mistos permanecem.

`Audit.lean` executa `#print axioms` e percorre tipos e corpos transitivamente,
incluindo auxiliares privados. O guard rejeita a sequência canônica, a
característica completada e os consumidores selecionados de sinais posteriores.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos. Sem `sorry`,
`admit`, `native_decide` ou axiomas matemáticos novos.

São 29 teoremas e sete definições públicos, em três módulos. As 36 raízes
auditadas percorrem 5.117 dependências de tipos e corpos, somente com os três
axiomas padrão permitidos. O guard de ausência da sequência canônica e da
característica completada passou para todos os resultados novos.

`validate.py` recompila os 23 ancestrais efetivamente importados e verifica seus
hashes contra a base, compila explicitamente os novos módulos e Audit com
warnings como erros, executa `lake build --wfail` e as auditorias Foundation,
Geometry e Analysis. Os comandos e resultados ficam em
`evidence/validation.json`; fontes, pins e trabalho antigo protegido, em
`source-provenance.json`, `upstream.json` e `preservation.json`. A raiz Lake
sozinha não inclui estes módulos de pesquisa.
Nesta execução, **os 14 comandos passaram com código de saída zero**, assim
como as verificações de preservação das fontes, pins e trabalho antigo.
`MANIFEST.sha256` permite conferir os arquivos entregues com
`sha256sum -c MANIFEST.sha256` nesta pasta.

## E — Próxima obrigação mínima

A generalização agora tem uma identidade concreta a confrontar com a fonte.
O primeiro alvo é formalizar, para todo coeficiente finitamente suportado c,
o numerador do comutador linear, mantendo explícitos os dois coeficientes iniciais:

\[
M S(C_\eta[p_1]c)\stackrel{?}=
\eta^{-1}(Sc-c_0\phi_0-c_1\phi_1)-\eta M^2Sc.
\]

Essa igualdade ainda não faz parte do certificado atual. Ela evita introduzir
uma inversa não limitada de M e localiza os dados que uma extensão all-order
precisa preservar. Depois, deve ser confrontada com os pesos binomiais e
fatoriais originais para calibrar `P_{m-2}(C)` no bordo de ordem m.
Reutilizar `coefficientShift` e `finiteCoefficientValve_two_traces`, de
`NativeCompletedFiniteGreenResidual.lean`, em vez de reconstruir a TFVD.

Os sinais escalares de P já estão demonstrados; falta a identificação do mesmo
kernel físico em todas essas ordens. Mesmo essa identificação resolveria uma
lei espacial da resposta linear, não a positividade all-order do residual finito.
A obrigação principal continua sendo o sinal da soma completada depois de
conservar e cancelar seus termos dominantes, com a resposta não linear original.

Reprodução no servidor `llm`, na pasta desta investigação:

```bash
python3 validate.py
```

Entrega em PR draft sobre a PR #96, sem merge automático. Main, fontes, pesos,
amplitudes, métrica, pins e trabalhos anteriores permanecem preservados.

**Fim do relatório.**
