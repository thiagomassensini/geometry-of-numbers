# Quarto pivô material: certificado racional da fonte e controle do limiar

## Resultado e fronteira formal

O certificado racional da **mesma fonte theta canônica** produz

\[
1.6662793746706138\cdot10^{-26}<p_3<1.6662826488940780\cdot10^{-26},
\]

com os extremos exatos, conservadores, em `certificate.json`. Os decimais acima são apenas apresentação; para uma afirmação decimal arredondada segura, use

\[
\boxed{1.6662793\cdot10^{-26}<p_3<1.6662827\cdot10^{-26}}.
\]

O limiar do PR #21 também foi incluído no cálculo:

\[
9.203801104615476\cdot10^{-28}<B-c_9<9.203819189998994\cdot10^{-28}.
\]

A afirmação decimal conservadora é `9.2038e-28 < B-c9 < 9.2039e-28`.

**Isto ainda não é um teorema Lean incondicional de positividade da fonte.** O cálculo é uma certificação computacional com aritmética racional, acompanhada da justificativa analítica abaixo. O Lean verifica a implicação quantitativa da caixa theta para o pivô e para o limiar, além de ingredientes analíticos independentes: a cota exponencial, a decomposição literal da fonte e a estimativa do restante infinito dos modos. A aplicação completa da quadratura finita aos integrais ainda não foi portada para o kernel. Não existe axioma novo nem teorema que afirme a caixa sem sua prova.

## Proveniência

- `geometry-of-numbers`: base `ac0fe970edeac46a43085960d93d85d7cc4aa17e`, merge do PR #21. A escadaria e o pareamento material são os dos PRs #20/#21.
- `carry-self-adjoint-operator`: consulta em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; nenhum arquivo alterado.
- `CompletedNativeXiThetaMoments.lean`: momentos integrais da fonte e identidades com os momentos cosseno.
- `CompletedNativeAllOrderMomentUpperBound.lean`: coeficientes característicos cosseno/fatorial.
- `CompletedNativeRealWeylMoments.lean`: recorrência literal dos momentos logarítmicos.
- `CompletedNativeThetaCubicQuadrature.lean` e Mathlib Taylor: convenção conservadora do erro de Taylor usada na nova quadratura escalar.
- Todos os pins Lean/Mathlib/GreenFrame permanecem iguais. O cache histórico e `momentos` servem somente como regressão diagnóstica.

## O que está sendo certificado

Escrevemos `h_n` para os momentos canônicos e `A_p` para `completedNativeThetaTailMoment p`. Não se cria outra fonte:

\[
\Theta(u)=2\sum_{m=1}^{\infty}e^{u/2-\pi m^2e^{2u}},\qquad
A_p=\int_0^\infty u^p\Theta(u)\,du.
\]

São usados exatamente

\[
c_0=\tfrac12-A_0/4,\qquad
c_n=(-1)^n\left(\frac{A_{2n-2}}{(2n-2)!}-\frac{A_{2n}}{4(2n)!}\right),
\]

\[
h_n=\frac{-(n+1)c_{n+1}-\sum_{k<n}h_kc_{n-k}}{c_0},
\qquad K(i,j)=h_{i+j+2}-h_{i+1}h_{j+1}/h_0.
\]

A eliminação é a original: `R0=K` e `R_(r+1)(i,j)=R_r(i,j)-R_r(i,r)R_r(r,j)/R_r(r,r)`. Os dois argumentos são conservados em todos os produtos; o programa não troca produtos ordenados por sinais atribuídos.

O alvo é `p3=R3(3,3)`, o quarto pivô do **bloco residual par**, correspondente ao quinto pivô Hankel não deslocado após restaurar o canal central. Não é o pivô histórico da oitava fonte do setor ímpar.

O limiar é calculado sem usar `h8` para defini-lo:

\[
T=\frac{h_4^2}{h_0}
+\frac{K(3,0)K(0,3)}{p_0}
+\frac{R_1(3,1)R_1(1,3)}{p_1}
+\frac{R_2(3,2)R_2(2,3)}{p_2},
\]

\[
B=-\frac{\sum_{k<8}h_kc_{8-k}+c_0T}{9},\qquad
c_9=\frac{A_{18}-1224A_{16}}{4\,18!},\qquad
c_0p_3=9(B-c_9).
\]

## Justificativa analítica do certificado

### 1. Aritmética e exponenciais

`certify.py` usa somente `Fraction`, inteiros e arredondamento **para fora** a múltiplos de `10^-70`. Todos os produtos verificam os quatro extremos; divisões cujo intervalo contém zero são recusadas. `float` aparece apenas na apresentação JSON, sem decidir nenhuma cota ou sinal. As condições do certificado continuam ativas; a execução com `python -O` é recusada.

As cotas de pi são as de 20 casas do Mathlib. Para `0 <= x <= 1024`, aplica-se o polinômio de Taylor de 40 termos em `x/1024`, com resto geométrico

\[
S_{39}(y)\le e^y\le S_{39}(y)+\frac{41y^{40}}{40\,40!},\quad 0\le y\le1,
\]

seguido de dez elevações ao quadrado intervalar, isto é, potência 1024. Para argumentos negativos usa-se o recíproco. `theta_certificate_exp_bounds` verifica no Lean a fórmula real subjacente. A implementação intervalar preserva os arredondamentos intermediários; nenhuma avaliação exponencial de máquina entra no certificado.

### 2. Quadratura dos três modos retidos

Integramos separadamente `F_m(u)=2 exp(u/2-pi*m^2*exp(2u))`, para `m=1,2,3`, até os cutoffs `3/2`, `1` e `3/4`, respectivamente. A malha principal é `1/64`: 208 células no total. A regressão usa `1/128`: 416 células.

Para `q=pi*m^2*exp(2u)`,

\[
F_m^{(r)}(u)=P_r(q)F_m(u),\quad P_0=1,
\quad P_{r+1}(q)=(\tfrac12-2q)P_r(q)+2qP_r'(q).
\]

Essa recorrência resulta da regra do produto e de `q'=2q`. Todas as derivadas usadas aqui são escalares dos modos exponenciais; não se postulou diferenciabilidade adicional do estado global em Hilbert. Os polinômios são calculados exatamente. O teste de regressão compara `P4=1/16-39q+166q^2-112q^3+16q^4` com a fórmula já formalizada.

Em cada célula `[a,b]`, `q` é crescente e `F_m` é decrescente, pois `q>=pi>3`. Portanto, se `Q` limita `q(b)` por cima e `U` limita `F_m(a)`,

\[
|F_m^{(16)}(u)|\le U\sum_j |[q^j]P_{16}|Q^j=:C.
\]

A expansão até grau 15 satisfaz o limite conservador de Taylor

\[
\left|F_m(x)-\sum_{r<16}\frac{P_r(q(a))F_m(a)}{r!}(x-a)^r\right|
\le\frac{C(x-a)^{16}}{15!}.
\]

O denominador é deliberadamente `15!`, compatível com a convenção de `taylor_mean_remainder_bound`; não se substituiu pelo limite mais forte `16!` sem prova.

A integração ponderada é exata, pois todos os coeficientes de

\[
W_{p,r}=\int_a^b x^p(x-a)^r\,dx
=\sum_{k=0}^p\binom pk a^{p-k}\frac{(b-a)^{k+r+1}}{k+r+1}
\]

são não negativos. Isso permite transportar intervalos dos coeficientes diretamente para os integrais e acrescentar `[-C W_(p,16)/15!, C W_(p,16)/15!]`.

**Fronteira Lean:** a recorrência geral dos polinômios, a instanciação das 208 células e sua agregação ainda não possuem um replay completo no kernel. Os intervalos não são importados como fatos Lean.

### 3. Caudas dos modos retidos

Para `L>0`, `v>=0`, `qL=pi*m^2*exp(2L)`, usa-se `exp(2v)>=1+2v` e `1+v/L<=exp(v/L)`:

\[
(L+v)^pF_m(L+v)\le
L^pF_m(L)\exp[-(2qL-\tfrac12-p/L)v].
\]

Todos os denominadores `s=2qL-1/2-p/L` são verificados positivos, para `p=0,2,...,18`. A cauda inteira recebe o intervalo

\[
0\le\int_L^\infty u^pF_m(u)\,du\le
\frac{L^pF_m(L)}{2qL-1/2-p/L},
\]

com `qL` limitado por baixo e `F_m(L)` por cima. Nenhuma cauda é simplesmente descartada.

### 4. Modos infinitos restantes

Para `m=4+j`, `j>=0`, temos `m^2 >= 16+8j`, `pi>=3` e `exp(2u)>=1+2u`. Daí

\[
2\sum_{m\ge4}e^{u/2-\pi m^2e^{2u}}
\le\frac{2e^{-48}}{1-e^{-24}}e^{-95u}
\le10^{-20}e^{-95u}.
\]

A última estimativa usa `exp(-24)<=1/2` e `exp(48)>4*10^20`. `theta_tail_after_three_le` prova no Lean a cota pontual da soma infinita original, e `theta_three_mode_split` prova a decomposição literal da fonte. O certificado acrescenta, para cada `p`,

\[
\boxed{0\le\text{restante de }A_p\le\frac{p!}{10^{20}95^{p+1}}}.
\]

A avaliação do integral exponencial é a identidade gamma elementar. Sua aplicação ponderada a cada caixa ainda integra a fronteira de formalização do certificado.

### 5. Propagação conjunta até o limiar

Somente depois de reunir as contribuições completas de cada momento, os intervalos passam pelas recorrências de `c`, `h`, `K`, `R`, `T` e `B`. Todos os três pivôs antigos são estritamente positivos em seus intervalos; as divisões são legitimadas pelos mesmos intervalos. Isso controla conjuntamente o termo novo e os acoplamentos antigos. Não se toma o contraste theta preciso e um limiar meramente aproximado.

O contraste `1224 u^16-u^18` muda de sinal longe do centro. Sua cauda negativa é conservada: o programa combina a cota inferior de `A16` com a superior de `A18`, sem presumir positividade pontual desse contraste.

A margem também pode ser escrita como

\[
1224A_{16}-A_{18}+4\,18!B>2.3570\cdot10^{-11}.
\]

## Teoremas e status

| Resultado | Status |
|---|---|
| `theta_certificate_exp_bounds` | Provado no Lean, sem hipótese física nova |
| `theta_mode_after_three_le` | Provado no Lean, para a fonte original |
| `theta_tail_after_three_le` | Provado no Lean, cauda infinita dos modos |
| `theta_three_mode_split` | Provado no Lean, decomposição literal |
| Caixas `A0,...,A18` de `certificate.json` | Certificado racional com justificativa analítica escrita; falta replay analítico completo no Lean |
| `material_fourth_bounds_of_theta_box` | Provado no Lean **condicional** às dez caixas explícitas da fonte |
| `material_fourth_critical_margin_of_theta_box` | Provado no Lean **condicional**, para a combinação material original |
| `material_fourth_posDef_of_theta_box` | Provado no Lean **condicional**, bloco residual par 4x4 |
| `material_fourth_cholesky_of_theta_box` | Provado no Lean **condicional**, fatoração exata original |
| Positividade da fonte em todas as ordens | Aberto |
| Identificação do Gram com o transporte físico global | Obrigações anteriores preservadas |

A hipótese `material_fourth_theta_box` aponta para **dez integrais theta efetivos**, com extremos literais gerados para fora. Não é um campo livre, não define estados por um Gram e não muda as constantes. A ausência da prova analítica Lean dessa hipótese é explícita no nome e no tipo de todos os resultados condicionais.

O resultado finito não fornece margem uniforme para os próximos pivôs nem justifica uma extensão automática a toda a hierarquia.

## Reprodução e validação

No servidor `llm`, a partir da raiz do repositório:

```sh
python3 research/material-pivot-certificate/certify.py --grid 64 --order 16 --out /tmp/carry-pivot-coarse.json
python3 research/material-pivot-certificate/certify.py --grid 128 --order 16 --out /tmp/carry-pivot-refined.json
python3 research/material-pivot-certificate/check_certificate.py /tmp/carry-pivot-coarse.json --refinement /tmp/carry-pivot-refined.json
python3 research/material-pivot-certificate/generate_lean.py --certificate research/material-pivot-certificate/certificate.json --out /tmp/carry-pivot-replay.lean
PATH=/home/thlinux/.elan/bin:$PATH bash scripts/audit-material-pivot-certificate.sh /home/thlinux/carry-self-adjoint-operator
PATH=/home/thlinux/.elan/bin:$PATH lake build --wfail
PATH=/home/thlinux/.elan/bin:$PATH bash scripts/audit-foundation.sh
PATH=/home/thlinux/.elan/bin:$PATH bash scripts/audit-geometry.sh
PATH=/home/thlinux/.elan/bin:$PATH bash scripts/audit-analysis.sh
```

O gerador emite o bloco marcado em `CanonicalPivotCertificate.lean`; não altera automaticamente outro repositório. O novo script compila a comparação canônica anterior como módulo de pesquisa e a importa, preservando literalmente seu arquivo de origem. `IntervalHelpers.lean` é a fonte do pequeno suporte de intervalos emitido. Os novos roots públicos da comparação têm `#assert_central_comparison_axioms` e `#print axioms` explícitos. A auditoria permite somente `propext`, `Classical.choice` e `Quot.sound`, conforme a política Analysis; não permite `sorryAx`.

A regressão verifica produtos com sinais mistos, recíprocos, recusa de denominador atravessando zero, o polinômio derivativo de quarta ordem, o replay dos extremos e a inclusão dos intervalos refinados nos grossos. A opção `--cache` compara o cache histórico apenas como diagnóstico e não participa da certificação.

## Próxima obrigação exata

Formalizar `material_fourth_theta_box` a partir da própria definição integral: derivadas escalares de ordem 16, cotas das células racionais, caudas retidas e agregação ponderada. Com essa prova, os resultados condicionais já verificam a margem, a direção crítica, a positividade do bloco par e a fatoração original. A etapa restante não é outra conjectura de positividade: é a transferência verificável do certificado analítico finito para os tipos Lean já preparados.
