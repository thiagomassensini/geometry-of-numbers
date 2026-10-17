# Certificado integral do quarto pivô par material

**Certificado integral incondicional verificado pelo kernel do Lean. Validação reproduzível completa aprovada.**

Base: `geometry-of-numbers` em `0ec56d57651c99fa8fd24a5e1d268558bc05ac77`
(merge do PR #22). Consulta externa, sem alterações: `carry-self-adjoint-operator`
em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

## Resultado e alcance

O resultado refere-se ao mesmo quarto pivô par material `carryMaterialFourthPivot`,
denotado por $p_3$. A margem racional demonstrada pelo certificado é

$$
\frac{16}{10^{27}}<p_3<\frac{17}{10^{27}}.
$$

São limites do pivô original, sem modificar sua fonte, seus pesos ou sua
normalização. A caixa de integrais usada é mais larga que a caixa auxiliar do
PR #22; sua largura permite uma verificação aritmética menor e ainda decide o
mesmo sinal. A implicação mais estreita do PR #22 permanece disponível com a
hipótese específica daquela caixa.

A fonte theta é infinita. O resultado de positividade refere-se ao bloco material
$4\times4$ e à sua combinação crítica, sem uma afirmação para todos os tamanhos.
A margem de um pivô não é automaticamente uma cota do menor autovalor do bloco.
Esse é o quarto pivô do residual par (quinto pivô Hankel após repor o canal
central), não o pivô histórico da oitava fonte do setor ímpar.

## Fonte e normalizações efetivamente utilizadas

Escrevemos $A_p=\texttt{completedNativeThetaTailMoment}\ p$. Literalmente,

$$
A_p=\int_{u>0}u^p\Theta(u)\,du,\qquad
\Theta(u)=2\sum_{m\ge1}\exp\left(\frac u2-\pi m^2e^{2u}\right).
$$

O índice dos modos no código começa em zero: `thetaMode n` é duas vezes
`XiThetaCosine.thetaTailMode n`, portanto corresponde ao inteiro $m=n+1$.
O parâmetro $u$ é a variável da integral theta; não é identificado com o tempo
material, com a profundidade ou com uma altura espectral.

As declarações canônicas anteriores fornecem

$$
c_0=\frac12-\frac{A_0}{4},\qquad
c_n=(-1)^n\left(\frac{A_{2n-2}}{(2n-2)!}-
\frac{A_{2n}}{4(2n)!}\right),\quad n\ge1,
$$

$$
c_0h_n+\sum_{k<n}h_kc_{n-k}=-(n+1)c_{n+1}.
$$

Aqui $c_n$ é `completedNativeRealEvenCharacteristicCoefficient n` e $h_n$ é
`canonicalCompletedNativeLogDerivativeMoment n`. O pareamento material anterior
é reutilizado pela identidade `material_even_pairing_source`:

$$
E(i,j)=h_{i+j+2}-\frac{h_{i+1}h_{j+1}}{h_0}.
$$

Definimos apenas a notação para a eliminação já existente:

$$
R_0=E,\qquad p_r=R_r(r,r),\qquad
R_{r+1}(i,j)=R_r(i,j)-\frac{R_r(i,r)R_r(r,j)}{p_r}.
$$

O certificado mantém os produtos ordenados. Nenhum termo misto é removido
para obter o sinal.

## A obrigação integral

Reutilizam-se o limiar $T=\texttt{carryMaterialFourthSourceThreshold}$ e
$B=\texttt{material_fourth_characteristic_ceiling}$. O limiar conserva os
acoplamentos antigos e depende somente dos momentos até $h_7$:

$$
T=\frac{h_4^2}{h_0}
+\frac{E(3,0)E(0,3)}{p_0}
+\frac{R_1(3,1)R_1(1,3)}{p_1}
+\frac{R_2(3,2)R_2(2,3)}{p_2}.
$$

As identidades anteriores dão

$$
p_3=h_8-T,\qquad
B=-\frac{\sum_{k<8}h_kc_{8-k}+c_0T}{9},\qquad c_0p_3=9(B-c_9).
$$

A relação já formalizada com a própria fonte é

$$
c_9=\frac{A_{18}-1224A_{16}}{4\,18!}.
$$

Assim, o certificado fecha o enunciado integral

$$
-4\,18!\,B<\int_{u>0}(1224u^{16}-u^{18})\Theta(u)\,du.
$$

O peso desta última integral tem uma parte negativa. A prova controla $A_{16}$
e $A_{18}$ completos e usa a identidade linear entre eles; não supõe que o
peso seja não negativo em toda a semirreta.

## Controle analítico das integrais

Para cada modo real $F_m(u)=2\exp(u/2-\pi m^2e^{2u})$, a recorrência racional

$$
P_0=1,\qquad P_{r+1}(q)=(1/2-2q)P_r(q)+2qP'_r(q)
$$

fornece $F_m^{(r)}(u)=P_r(\pi m^2e^{2u})F_m(u)$ em qualquer ordem finita.
Isso é regularidade escalar dos modos; nenhuma nova derivada de um estado
Hilbertiano global é postulada. A tabela racional até a ordem 16 é conferida
contra essa recorrência, com um lema geral para os coeficientes fora do suporte.

A quadratura usa Taylor de grau 15 em 208 células de largura $1/64$:

| Modo $m$ | Cutoff | Células |
|---|---:|---:|
| 1 | $3/2$ | 96 |
| 2 | $1$ | 64 |
| 3 | $3/4$ | 48 |

A fórmula exata para os pesos é

$$
W_{p,r}(a,b)=\int_a^b u^p(u-a)^r\,du
=\sum_{k=0}^p\binom pk a^{p-k}
\frac{(b-a)^{k+r+1}}{k+r+1}.
$$

O erro por célula tem o fator conservador
$C\,W_{p,16}(a,b)/15!$, conforme a convenção do teorema de Taylor do Mathlib.
Os coeficientes de Taylor conservam seus sinais.

Para a cauda de cada modo retido, com $L>0$ e denominador positivo,

$$
0\le\int_L^\infty u^pF_m(u)\,du\le
\frac{F_m(L)L^p}{2\pi m^2e^{2L}-1/2-p/L}.
$$

Para todos os modos omitidos, reutiliza-se o controle do PR #22 e integra-se
seu majorante:

$$
0\le\int_0^\infty u^p\sum_{m\ge4}F_m(u)\,du
\le\frac{p!}{10^{20}\,95^{p+1}}.
$$

`completedNativeThetaTailMoment_eq_three_and_remainder` conserva exatamente o
resto infinito. `mem_exactFullThetaMomentBox` transporta essas identidades para os
intervalos aritméticos para $p\le18$; `mem_tabledFullThetaMomentBox` reaproveita
o mesmo resultado mediante igualdades verificadas dos caches.

## Verificador aritmético e cache fiel

`FixedInterval` usa inteiros com escala computacional $10^{60}$ e arredondamento
para fora. A falha de um cálculo produz `Box.all`; esse valor não pode passar uma
checagem final de inclusão em uma caixa finita ou de positividade estrita.

A exponencial usa 20 termos para $\exp(x/128)$ e a identidade exata
$\exp(x)=\exp(x/128)^{128}$. O fator 128 é apenas parte do algoritmo de avaliação;
não altera amplitudes, fontes ou métricas. As cotas vêm de `Real.exp_bound'`.

O cache contém 211 nós: os 208 pontos iniciais de célula e seus três extremos
finais. Cada argumento e cada valor de modo é comparado ao programa original
por redução do kernel, em `ArgNodeChecks` e `ModeNodeChecks`.
`fullThetaMomentBox_eq_cached` demonstra igualdade do programa inteiro,
incluindo as parcelas assinadas e todas as caudas.

Um segundo cache contém os 16 coeficientes de Taylor assinados e o majorante
de erro de cada uma das 208 células. `QuadratureNodeCheck0`–`3` verificam todas
as entradas por redução do kernel. A tabela depende somente dos modos theta,
sem usar momentos ou pivôs como dados. `TabledSourceEquivalence` identifica
o programa tabelado com a quadratura da fonte.

Os pesos na malha são racionais exatos:

$$
W_{p,r}(j/64,(j+1)/64)=
64^{-(p+r+1)}\sum_{k=0}^p\binom pk\frac{j^{p-k}}{k+r+1}.
$$

`rationalGridWeight_eq` prova essa fórmula. Multiplicar um coeficiente
intervalar pelo peso exato usa um único arredondamento para fora; não se
altera o peso. `Nat.fast_choose` é identificado com `Nat.choose` pelo teorema
correspondente do Mathlib. Os dez momentos usados são $A_0,A_2,\ldots,A_{18}$.

O gerador e a execução `#eval` produzem apenas testemunhas numéricas. A validade
não depende de confiar neles. As checagens matemáticas usam `decide +kernel`,
com auditoria transitiva de axiomas; não usam `native_decide`.

## Declarações finais

Em `IntegralCertificate.lean`:

- `material_theta_integral_input`: inclusão dos integrais reais na caixa.
- `material_fourth_pivot_bounds_integral`: margem racional de $p_3$.
- `material_fourth_pivot_pos_integral`: estrita positividade.
- `material_fourth_theta_integral_gate`: a desigualdade integral assinada.
- `material_fourth_block_posDef_integral`: positividade definida do bloco $4\times4$.
- `material_fourth_critical_positive_integral`: energia positiva da combinação crítica.
- `material_fourth_cholesky_integral`: fatoração de Cholesky finita exata.

## Status

| Item | Status |
|---|---|
| Derivadas escalares, quadratura e caudas completas | Provado |
| Pertencimento da fonte ao intervalo computável | Provado |
| Igualdade do cache ao programa original | Provado |
| Dez inclusões aritméticas e composição final | Provado em Lean |
| Implicação para a caixa mais estreita do PR #22 | Condicional àquela caixa; preservada |
| Positividade para todo tamanho | Aberto |
| Novos no-gos | Nenhum estabelecido nesta rodada |
| Identificações físicas globais adicionais e operador infinito | Fora deste certificado |

## Fronteira que permanece aberta

A recorrência de Schur é algébrica e a fatoração de Cholesky é reutilizada.
Elas não fornecem por si mesmas o sinal do próximo pivô. O avanço específico
é retirar a hipótese numérica da caixa de momentos para este quarto pivô,
provando suas dez inclusões diretamente sobre as integrais da fonte.

A fonte é infinita, mas o bloco certificado tem tamanho fixo. Para cada novo
bloco ainda seriam necessárias estimativas integrais suficientes e margens
positivas. Uma regra de positividade uniforme na ordem continua ausente.
Também não se infere uma nova identificação entre o Gram de um carrier físico
e o kernel canônico, nem um resultado espectral para o operador infinito.

## Validação e proveniência

- Lean `v4.32.0`.
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Build geral: `lake build --wfail`, 8.841 alvos, aprovado.
- Build dedicado completo: 47 módulos com avisos como erros, aprovado.
- Regeneração literal das três tabelas e inclusões dos dez momentos: aprovada.
- Auditorias de Foundation, Geometry e Analysis: aprovadas.
- Os módulos novos ficam em `research/`; exigem o build dedicado, além do build
  geral. `Audit.lean` guarda os 221 nomes públicos listados em `public-roots.txt`,
  verificando axiomas transitivos nos tipos e corpos. O footprint permitido é
  `propext`, `Classical.choice`, `Quot.sound`; não é uma prova livre de axiomas.
- `check_public_roots.py` confere a cobertura do inventário. As três regressões
  comparam o primeiro modo, o polinômio de quarta derivada e a identidade theta
  assinada com as declarações anteriores.

O script `audit-material-integral-certificate.sh` reproduz a verificação contra
os pins e o checkout do operador indicados. Nenhuma fonte histórica, manifesto,
normalização ou módulo preexistente é modificado por esta rodada.


### Reprodução

No servidor `llm`, no checkout de `geometry-of-numbers`, com o checkout fixado
`../carry-self-adjoint-operator` e seus artefatos de build disponíveis:

```bash
bash research/material-integral-certificate/audit-material-integral-certificate.sh
```

O script usa `-DwarningAsError=true` nos módulos dedicados, `lake build --wfail`
no projeto inteiro, redução `decide +kernel` nas verificações fechadas e as
três auditorias de zona. Regenera as testemunhas e compara literalmente as tabelas.
A concorrência padrão é dois processos; `CARRY_INTEGRAL_JOBS=1` permite reduzir o
uso de memória.

Nesta rodada, as dependências inalteradas dos PRs #21/#22 foram recompiladas
antes da composição. A repetição completa do grafo novo usa
`CARRY_INTEGRAL_REUSE_PR22=1`, que verifica a existência dos artefatos e a ausência
de alterações nas respectivas fontes contra o merge `0ec56d5`. Essa opção não
pula nenhuma verificação dos módulos novos. Os logs e hashes em `evidence/`
identificam a validação efetivamente executada, encerrada com código de saída 0.
`build-results.json` registra as 47 compilações; `Audit.log` mostra também os
tipos dos principais teoremas sem a hipótese auxiliar sobre os momentos.

Nenhuma worktree foi criada nesta rodada. As worktrees históricas e os dois
módulos C2 não rastreados no checkout do operador foram preservados.
