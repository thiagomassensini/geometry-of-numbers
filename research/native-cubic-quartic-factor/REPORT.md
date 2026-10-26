# Fator cúbico quártico, cruzamentos ordenados e família positiva de duas fontes

**PARTIAL para a positividade canônica all-order. A obrigação quártica da
PR #100 está fechada.** A fatoração candidata foi identificada com o
comutador original, conservando seu halo. Dela se deduz a margem

\[
\boxed{U_{3,4}\ge\frac3{17920}>0\qquad(0<\eta<1).}
\]

Também foram demonstradas cotas negativas para os dois cruzamentos ordenados
entre os perfis nativos de ordens 4 e 2. Mantendo esses cruzamentos, a fonte
`d₄−a q` tem coeficiente cúbico estritamente positivo para `a≥0`.
Isso não é uma positividade em todas as direções nem o sinal do residual
canônico completado.

Base exata: `6a3ab21c1c986b809c49f0d26ff1ede034ef425b`, PR #100,
branch `agent/native-cubic-tfvd-numerator`. Continuação em
`agent/native-cubic-quartic-factor`, destinada à PR #100, sem merge automático.
Main: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

Reutilizamos as colunas físicas `φ_j=completedNativeChiralCauchyFeature j`,
a síntese `S=physicalCauchySynthesis` e os operadores originais

\[
M=\texttt{physicalRadialAdvance},\quad C=I-M,\quad
R_\eta=(I-\eta M)^{-1},\quad G_\eta=\eta M R_\eta^2.
\]

u∈[0,1] é a coordenada do carrier Cauchy existente. A prova usa esse espaço e
sua métrica já construída; não usa caixas dos integrais theta ou momentos
canônicos como entradas. As identidades com resolvente usam `0<η<1`.

Os dois perfis nativos desta rodada são

\[
q=\texttt{curvatureInput}=(-1/2,1,-1/2),\qquad
d_4=\texttt{fourthShape}=(1,-4,6,-4,1)/24.
\]

O sinal negativo do perfil de ordem dois e o fatorial 4! são os originais.
Não se troca q por uma versão com sinal escolhido. A calibração radial da
PR #99 conserva o passo `δ_k=i/(k+1)`: as entradas radiais de ordens 2 e 4
correspondem a `(k+1)²q` e `δ_k⁻⁴d₄=(k+1)⁴d₄`. O índice radial k não é
profundidade Carry nem endereço material.

Teoremas preexistentes efetivamente reutilizados:

- PR #96, `CurvatureKernel.lean`: `green_inner_transport`,
  `curvature_resolvent_advance`, `gradient_pairing`, autoadjunção e comutação.
- PR #96, `NativeCoefficient.lean`: `native_curvature` e
  `native_gradient_norm_lower`, com norma ao quadrado pelo menos 1/60.
- PR #97, `FourthBoundaryDefect.lean`: `fourthShape` e seus pesos explícitos.
- PR #97, `BoundaryFactor.lean`: `quarticVector`, `quarticGradient`,
  `quartic_resolvent_advance`, `complement_twice_pairing`,
  `quartic_base_pairing`, `quartic_gradient_as_complement`.
- PR #97, `QuarticCoefficient.lean`: `native_quartic_vector` e
  `native_quartic_gradient_lower`, com norma ao quadrado pelo menos 1/280.
- PR #99, `BoundaryOperator.lean`: as identidades de multiplicadores
  `multiplier_add`, `multiplier_pow` e `complement_multiplier`.
- PR #100: `cubic_commutator_succ`, `cubicKernel`, sua identificação original,
  `cubic_three_input_expansion` e o controle quadrático do coeficiente cúbico.

Usamos a notação original

\[
K_3(c,d)=\langle Sc,G_\eta S(C_\eta[p_3]d)\rangle,
\qquad p_3(j)=(j+1)^3.
\]

A PR #100 já provou `U_{3,2}=Re K₃(q,q)≥1/20`. A PR #97 já identificou
`w₄=RηMC²φ₀` e provou `‖w₄‖²≥1/280`. Essas normas vêm da Gram Cauchy literal.

## B — O que foi demonstrado agora

### B.1 — Polinômios forçados e identificação vetorial

`QuarticPolynomials.lean` define somente os polinômios determinados pelos
pesos cúbicos sobre o stencil antigo:

\[
A_4=27I+26C+61C^2,\qquad
B_4=C^2(36I-120C+91C^2).
\]

São `quarticForward` e `quarticBackward`. Os teoremas
`quartic_forward_in_advance` e `quartic_backward_in_advance` provam

\[
A_4=114I-148M+61M^2,
\quad B_4=7I-76M+222M^2-244M^3+91M^4.
\]

`forward_as_multiplier` e `backward_as_multiplier` identificam esses mesmos
operadores com seus símbolos no intervalo físico. Não há coeficientes livres.

`quartic_cubic_commutator` demonstra o vetor original completo:

| Endereço | Coeficiente de Cη[p₃]d₄ |
| --- | --- |
| 1 | 19/(4η)−7η/24 |
| 2 | −37/(6η)+19η/6 |
| 3 | 61/(24η)−37η/4 |
| 4 | 61η/6 |
| 5 | −91η/24 |

O endereço zero é nulo por definição do comutador. O endereço 5 não é cortado:
`quartic_cubic_halo_nonzero` prova que seu coeficiente é não nulo para η>0.

Defina a expressão física limitada

\[
t_{4,\eta}(f)=\frac1{24}
\big[\eta^{-1}MA_4f-\eta MB_4f\big]
\quad(\texttt{quarticCubicTangent}).
\]

`quartic_cubic_tangent_native` prova primeiro a igualdade vetorial

\[
\boxed{t_{4,\eta}(\phi_0)=S(C_\eta[p_3]d_4).}
\]

A definição polinomial não substitui a fonte: sua igualdade com o comutador
literal, incluindo os coeficientes de bordo e o halo, é demonstrada antes de
qualquer desigualdade. A identificação nativa é essa especialização em φ₀;
não se anuncia uma comutação do peso de endereço p₃ com uma troca arbitrária
de estado físico.

### B.2 — Fatoração polarizada no mesmo Green

Escreva `q₄(f)=quarticVector f=C⁴f/24`,
`w₄(f)=quarticGradient eta ... f=RηMC²f` e

\[
H_4(\eta)=A_4-\eta^2B_4.
\]

Após as identidades de comutação dos polinômios originais,
`quartic_cubic_polarized` prova, para dois argumentos complexos independentes,

\[
\boxed{
\langle q_4(f),G_\eta t_{4,\eta}(g)\rangle
=\frac1{576}\langle w_4(f),H_4(\eta)w_4(g)\rangle.
}
\]

Só depois vem a diagonal real, em `quartic_cubic_diagonal`.
`native_quartic_cubic_identification` e `native_quartic_cubic_factor` chegam
ao kernel original:

\[
\boxed{
U_{3,4}:=\Re K_3(d_4,d_4)
=\frac1{576}\Re\langle w_4,H_4(\eta)w_4\rangle.
}
\]

É exatamente a candidata do relatório da PR #100. O fator 576 é 24².
O termo assinado `−η²C²(36I−120C+91C²)` permanece na identidade.

### B.3 — Margem quártica deduzida da métrica original

`quartic_backward_upper_positive` prova `B₄≼36C²` pelo símbolo
`x³(120−91x)≥0`, onde `x=1−u∈[0,1]`.
O teorema `quartic_margin_positive` conserva a resposta inteira e demonstra

\[
\begin{aligned}
H_4(\eta)-27I
={}&26C+(61-36\eta^2)C^2+\eta^2C^3(120I-91C)
\succeq0.
\end{aligned}
\]

Essa decomposição é uma igualdade do símbolo do mesmo multiplicador.
Seus termos têm sinal porque `0<η<1` e `0≤x≤1`, sem hipótese sobre h.
`quartic_margin_inner_lower` fornece `Re⟨f,H₄f⟩≥27‖f‖²`, e
`quartic_cubic_lower` transporta a cota ao pareamento original.

Usando a norma Cauchy anterior, os teoremas
`native_quartic_cubic_lower_bound` e `native_quartic_cubic_pos` concluem

\[
\boxed{U_{3,4}\ge\frac{27}{576}\frac1{280}
=\frac3{17920}>0.}
\]

As constantes vêm dos pesos do comutador, de 4! e da Gram física original.
Não são escolhidas para ajustar um momento ou um pivô.

### B.4 — Os dois cruzamentos ordenados, com sinais demonstrados

Use `v₂(f)=transportedGradient eta ... f=RηMCf` e o polinômio já certificado
na PR #100:

\[
B_2=7I-38M+37M^2,\qquad H_2(\eta)=19I-\eta^2B_2\succeq12I.
\]

Os teoremas `quartic_quadratic_polarized` e
`quadratic_quartic_polarized` são provados separadamente:

\[
\boxed{
\langle q_4(f),G_\eta t_{3,\eta}(g)\rangle
=-\frac1{48}\langle w_4(f),H_2(\eta)w_4(g)\rangle,
}
\]

\[
\boxed{
\langle d_f,G_\eta t_{4,\eta}(g)\rangle
=-\frac1{48}\langle v_2(f),H_4(\eta)v_2(g)\rangle.
}
\]

Aqui `d_f=physicalCurvature f` e `t₃,η` é o `cubicTangent` da PR #100,
calibrado no mesmo perfil q. Não se usa uma igualdade entre os dois
cruzamentos nem uma simetria Hermitiana não demonstrada.

As duas normas físicas anteriores fornecem
`native_quartic_quadratic_upper`, `native_quadratic_quartic_upper` e
`native_ordered_crosses_negative`:

\[
\boxed{
X_{42}:=\Re K_3(d_4,q)\le-\frac1{1120}<0,\qquad
X_{24}:=\Re K_3(q,d_4)\le-\frac3{320}<0.
}
\]

Ambos são pareamentos mistos originais, não energias auxiliares escolhidas
para fornecer um sinal.

### B.5 — Uma família positiva de duas fontes, preservando seus cruzamentos

`two_jet_expansion` conserva todos os quatro pareamentos de `d₄−a q`:

\[
\Re K_3(d_4-aq,d_4-aq)=U_{3,4}+a^2U_{3,2}-a(X_{42}+X_{24}).
\]

Portanto `two_jet_cone_lower` e `two_jet_cone_pos` demonstram, para a≥0,

\[
\boxed{
\Re K_3(d_4-aq,d_4-aq)
\ge\frac3{17920}+\frac{a^2}{20}+\frac{23a}{2240}>0.
}
\]

O coeficiente 23/2240 é `1/1120+3/320`. A restrição a≥0 está exposta e se
refere ao coeficiente livre da fonte. Ela não é outro nome para PosDef.
Não se escolhe a por uma positividade de momentos.

Essas cotas estão escritas nos perfis q e d₄ originais. Na família radial da
PR #100, a entrada sem semente tem os fatores `(k+1)⁴d₄−a_rad(k+1)²q`.
A correspondente coordenada do perfil é `a=a_rad/(k+1)²`; não se omitem os
fatores radiais nem se confunde a escala com uma mudança de câmera.

## C — Obstruções e limites da conclusão

Esta rodada fecha uma identidade que antes era candidata e prova os sinais
dos dois cruzamentos. Não demonstra que o kernel cúbico seja positivo em
todo o espaço gerado por q,d₄ ou em todas as combinações com a semente.
O conjunto `d₄−a q`, a≥0, não é um subespaço vetorial.

O contraexemplo da PR #100 na fonte `e₀=Finsupp.single 0 1` continua válido:
`Re K₃(e₀,e₀)<0`. Assim, a prova dessa família não permite descartar a contribuição
da semente em `J₄−aJ₂−bJ₀`, nem converter K₃ numa Gram positiva do problema
canônico. Nenhuma nova impossibilidade da geometria é afirmada.

Também não se infere uma positividade Hankel all-order, uma margem relativa
fixa entre incidência e retorno ou o sinal do residual depois dos cancelamentos
com os demais pesos da resposta. O fator cúbico possui sua contribuição
assinada na resposta completada original. Todos esses termos continuam lá.
Os certificados finitos canônicos anteriores permanecem válidos.

## D — Auditoria e reprodução

São 37 teoremas e seis definições em quatro módulos novos:
`QuarticPolynomials.lean`, `QuarticFactor.lean`, `QuarticBound.lean` e
`MixedFactors.lean`. `Audit.lean` imprime axiomas e percorre tipos/corpos das
43 raízes públicas, com 5.233 dependências transitivas.

Todo resultado novo pertence ao grupo espacial: não depende da sequência
canônica, da característica completada ou dos consumidores de sinal
selecionados pelo guard. Só `propext`, `Classical.choice` e `Quot.sound`
são permitidos. Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos
novos.

Os inputs complexos independentes são preservados antes da especialização
real. O Green e seu resolvente limitado são os originais, sem truncamento de
cauda. A identificação nativa ocorre nos mesmos coeficientes finitos, sem
nova métrica, amplitudes, pesos, câmera ou normalização.

`validate.py` recompila os 35 ancestrais de pesquisa efetivamente importados,
verifica seus hashes contra a base, compila explicitamente os quatro módulos
e a auditoria com warnings como erros, executa `lake build --wfail`,
Foundation/Geometry/Analysis e a preservação da base e dos trabalhos antigos.
A raiz Lake sozinha não inclui os módulos novos de pesquisa. Os comandos,
códigos de saída e tempos ficam em `evidence/validation.json`; fontes, pins e
trabalho protegido, em `source-provenance.json` e `preservation.json`.

Os **15 checks passaram com código de saída zero**, incluindo as
compilações explícitas, o build raiz com `--wfail` e as três auditorias.
`preservation.json` registra preservação de fontes, pins, main e trabalho
preexistente. O manifesto `MANIFEST.sha256` permite conferir todos os
arquivos versionados desta entrega com `sha256sum -c MANIFEST.sha256`.
A aprovação local não é uma afirmação sobre execução de CI externo.

Para recriar a worktree no servidor `llm` após sua remoção:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-cubic-quartic-factor \
  agent/native-cubic-quartic-factor
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-cubic-quartic-factor/.lake
```

Na pasta `research/native-cubic-quartic-factor` dessa worktree:

```bash
python3 validate.py
```

## E — Próxima obrigação mínima

Os dois blocos diagonais cúbicos e os dois cruzamentos entre ordens 2 e 4
agora têm identidades físicas e cotas. O menor próximo alvo é calibrar os
quatro cruzamentos ordenados restantes com a semente positiva
`e₀=Finsupp.single 0 1`, preservando sua distinção do antigo `seedInput=−e₀`.

Com `r=RηMφ₀`, `v₂=Cr` e `w₄=C²r`, confrontar e formalizar as candidatas

\[
\begin{aligned}
\Re K_3(q,e_0)&\stackrel{?}=\frac{7\eta^2}{2}\|v_2\|^2,\\
\Re K_3(e_0,q)&\stackrel{?}=-\frac12\Re\langle r,H_2(\eta)r\rangle,\\
\Re K_3(d_4,e_0)&\stackrel{?}=-\frac{7\eta^2}{24}\|w_4\|^2,\\
\Re K_3(e_0,d_4)&\stackrel{?}=\frac1{24}\Re\langle r,H_4(\eta)r\rangle.
\end{aligned}
\]

Essas quatro igualdades não são novos teoremas desta entrega. A prova deve
começar pelas versões complexas polarizadas em dois argumentos e pelo
comutador literal da semente. Só depois se toma a diagonal real.

Com isso, será possível confrontar o setor cúbico inteiro da família livre
`J₄−aJ₂−bJ₀`, incluindo a direção negativa da semente e todos os termos em b.
Depois ainda faltará a lei Taylor com resto na ordem necessária e os
cancelamentos entre setores antes da parte finita de Schur da PR #41.
Nenhum desses passos é autorizado por extrapolar os sinais desta rodada.

Entrega em PR draft sobre a PR #100, sem merge automático. Main, fontes,
amplitudes, pesos, métrica, pins e arquivos antigos são preservados. Relatório
integral, logs e manifesto são copiados e conferidos localmente antes da
remoção somente da worktree temporária desta tarefa.

**Fim do relatório.**
