# Bloco misto do residual material e transporte confluente pela válvula

## Resultado matemático

Foi construída uma leitura confluente com dois índices independentes do
**residual material já existente**, depois da síntese completa. Seus
coeficientes foram calibrados pela mesma fonte canônica. O primeiro bloco
misto, nas ordens de Taylor 2 e 4, tem quatro entradas ordenadas:

\[
\begin{pmatrix}C_2&B\\ B&C_4\end{pmatrix},\qquad
C_2=h_2-h_1^2/h_0,\quad
B=h_3-h_1h_2/h_0,\quad
C_4=h_4-h_2^2/h_0.
\]

O transporte preserva os dois argumentos antes de tomar a diagonal:

\[
\begin{aligned}
C_2xv+Bxw+Byv+C_4yw
={}&C_2\left(x+\frac B{C_2}y\right)
        \left(v+\frac B{C_2}w\right)+p_{0,2}yw,\\
p_{0,2}={}&C_4-B^2/C_2.
\end{aligned}
\]

O novo crosswalk identifica esse último escalar com o **terceiro pivô
ordinário de Schur existente**, sem definir um estado físico pela matriz.
A direção crítica \((x,y)=(-B/C_2,1)\) lê exatamente \(p_{0,2}\).

Reutilizando o certificado theta anterior para cinco fontes, obtemos

\[
\boxed{
p_{0,2}=\frac{\texttt{nativeSourceFiveEvenDiscriminant}}
                   {8(h_0h_2-h_1^2)}>0.
}
\]

Portanto

\[
\boxed{B^2<C_2C_4},\qquad
\boxed{C_2x^2+2Bxy+C_4y^2>0\quad\text{se }(x,y)\ne(0,0).}
\]

O sinal de cinco fontes já tinha prova. O avanço desta rodada é identificar
e controlar o cruzamento no residual material e transportá-lo ao balanço
completo da válvula. Não se anuncia um novo certificado theta nem uma prova
de positividade em ordem arbitrária.

## 1. Extração dos coeficientes da fonte efetiva

O módulo novo é
`GeometryOfNumbers/Analysis/CarryMaterialMixedSchur.lean`.

`carryScalarJetShift n f` itera as diferenças divididas centrais da própria
função. O funcional `carryKernelJet K p q` aplica primeiro a leitura de ordem
`p` no primeiro argumento e depois a de ordem `q` no segundo argumento.
As avaliações centrais usam as derivadas escalares existentes; em um germe
analítico, são coeficientes de Taylor normalizados pelos fatoriais.

Foi provada a comutação não trivial

\[
\operatorname{dslope}_{0,t}
 \bigl[x\mapsto\operatorname{dslope}f(x,u)\bigr]
=\operatorname{dslope}(\operatorname{dslope}f(0,\cdot))(t,u),
\]

com as hipóteses de diferenciabilidade escalares apropriadas. Os casos de
coincidência dos argumentos são tratados com derivadas, incluindo a origem.
Não se cancelam fatores nulos nesses casos.

A comparação externa utiliza `material_residual_centered_kernel`, que já
identificava o residual verdadeiro:

\[
R(t,u)=\operatorname{dslope}r(t,u)-A(t)A(u)/h_0,
\qquad A(t)=\operatorname{dslope}r(0,t).
\]

A identidade nova é uma consequência dessa igualdade, não a definição de
uma matriz escolhida antecipadamente. Se \(a_n\) denota o coeficiente de
Taylor da resposta material \(r\), a leitura complexa é

\[
\boxed{\operatorname{jet}_{p,q}R
 =a_{p+q+1}-a_{p+1}a_{q+1}/h_0.}
\]

As duas quadraturas são conservadas nessa igualdade complexa antes de
extrair a parte real. A proveniência dos coeficientes fornece, em toda ordem
finita e sem hipótese de sinal,

\[
\begin{aligned}
\operatorname{jet}_{2i,2j}R&=h_{i+j}-h_ih_j/h_0,\\
\operatorname{jet}_{2i+1,2j+1}R&=h_{i+j+1},\\
\operatorname{jet}_{2i,2j+1}R
&=\operatorname{jet}_{2i+1,2j}R=0.
\end{aligned}
\]

Esses índices são ordens de Taylor. Não são profundidades, câmeras,
endereços materiais ou índices espectrais.

A regularidade utilizada é analiticidade **escalar real** da resposta
completada, obtida do germe complexo já identificado por um transporte de
escalares explícito. Não se acrescentam derivadas fortes do estado global
em Hilbert, nem se promove uma derivada direcional a um jet holomorfo.

## 2. Leitura pelo balanço completo da válvula

O PR #18 já demonstrou

\[
\mathcal B_\eta(t,u)=d(t,u)R(t,u),\qquad
d(t,u)=2a^2tu\,\overline{F(t)}F(u)(u-t),
\]

com a escala original \(a\) e o valor completado original \(F\).
O novo `carryValveResidualFactor` apenas nomeia esse fator literal.

`carryValveConfluentReadout` observa \(\mathcal B_\eta/d\) onde \(d\ne0\),
e é estendido por zero fora desse conjunto. Essa extensão é **somente um
representante para observações centrais ordenadas**. Não é identificada
com um kernel em toda a diagonal: em particular, seu valor é zero em
\((t,t)\), enquanto não se afirma \(R(t,t)=0\).

A validade das observações é demonstrada antes de usá-las. Para todo `u`
suficientemente próximo de zero, prova-se uma igualdade de germes na
variável `t`, em zero:

\[
\text{leitura da válvula}(t,u)=R(t,u).
\]

Para \(u\ne0\), escolhe-se uma vizinhança de zero que evita \(t=u\);
\(F\ne0\) perto do centro e todos os demais fatores são verificados.
Nas duas linhas centrais, a extensão zero coincide com as identidades
preexistentes \(R(0,u)=R(t,0)=0\). A vizinhança pode depender de `u`.

Isso prova que **todos os jets confluentes ordenados finitos** da leitura
são os do residual verdadeiro, sem afirmar analiticidade conjunta da
extensão por zero. O bloco 2/4 e sua direção crítica são então transportados
exatamente para `carryValveMixedBlock`.

Na região regular, `carryValveConfluentReadout_physical` conserva literalmente

\[
\frac{G(X_t,X_u)-G(HX_t,HX_u)}{d(t,u)},
\]

onde os pares são os reduzidos já construídos. O complemento oculto continua
subtraído. O numerador reutiliza a expressão integral do PR #18, com sementes,
retorno ordinary, retorno clockado e conexão derivativa do dressing. Não se
retiram GG, GR, RG, RR nem cruzamentos para produzir o sinal.

## 3. Proveniência do controle de sinal

A identificação matricial usa as definições existentes `sourceMomentMatrix`,
`sourceMomentCoupling` e `sourceMomentSchur`. A solução do prefixo 2×2 é
verificada e substituída na mesma fórmula de Schur; o determinante não nulo
vem do discriminante já certificado.

O fator 8 na fórmula de sinal é obrigatório: os coeficientes da forma de
bordo de cinco fontes são \(2h_j\), e seu determinante cúbico carrega
\(2^3\). Esse fator é derivado no Lean; nenhuma normalização foi ajustada.

Também foi calibrada a integral theta original:

\[
c_0p_{0,2}
=\texttt{nativeXiPolynomialIntegral}
  (\texttt{nativeSchurThetaPolynomial}\ 0\ 2),\qquad c_0>0.
\]

O sinal vem de `nativeSourceFiveEvenDiscriminant_pos`, demonstrado no módulo
`CompletedNativeChiralReturnTenthSourceIntegral.lean`. Esse certificado usa
a fonte theta e suas correlações, não uma hipótese nova de positividade.

## 4. Declarações principais

No namespace `GeometryOfNumbers.Analysis`:

- `carryScalar_dslope_left_comm` e `carryScalar_dslope_row_shift`.
- `carryKernelJet_centered` e `carryKernelJet_germ`.
- `carryMaterialMixedBlock_sewing` e `carryMaterialMixedBlock_critical`.
- `carryValveConfluentReadout_physical`.

No namespace `CarryMaterialMixedSchurComparison`, no crosswalk externo
`research/material-central-calibration/CanonicalComparison.lean`:

- `material_residual_complex_jet_source`, `material_residual_jet_source` e
  as quatro calibrações de paridade.
- `material_mixed_entries`, `material_mixed_pivot_eq_schur` e
  `material_mixed_pivot_theta`.
- `material_mixed_pivot_pos`, `material_mixed_cross_dominance` e
  `material_mixed_block_pos`.
- `material_valve_confluent_row_germ`, `material_valve_confluent_jet`,
  `material_valve_mixed_block`, `material_valve_mixed_critical` e
  `material_valve_mixed_block_pos`.

## 5. Alcance e primeira obrigação que permanece

| Status | Resultado |
| --- | --- |
| PROVADO | Coeficientes mistos ordenados do residual efetivo, em toda ordem finita |
| PROVADO | Bloco 2/4, quatro cruzamentos, costura bilinear e direção crítica |
| PROVADO | Igualdade com o terceiro pivô ordinário e integral theta original |
| PROVADO POR REUSO | Sinal estrito do primeiro bloco misto, a partir do certificado anterior |
| PROVADO | Transporte dos jets para a leitura do balanço completo da válvula |
| NÃO AFIRMADO | Extensão conjunta da divisão pela diagonal não central |
| NÃO AFIRMADO | Troca de derivadas com limites dos prefixos ou parcelas Green separadas |
| ABERTO | Positividade para todas as famílias de tempos, em uma vizinhança comum |
| ABERTO | Positividade dos novos pivôs em toda ordem e realização como Gram físico positivo |

A fonte controla, portanto, esta primeira combinação que cancela o canal
principal. A positividade da matriz de coeficientes 2×2 não prova a
positividade do residual em amostras de tempo não nulas: o restante analítico
continua presente e ainda precisa de controle apropriado.

Para o próximo sinal finito ainda aberto na rota histórica, o alvo continua
sendo \(p_{1,3}>0\), isto é, a dominância das massas da fonte para
`nativeSchurThetaPolynomial 1 3`. A calibração de paridades desta rodada
explica onde o bloco deslocado aparece nas leituras confluentes materiais;
ela não fornece esse sinal novo.

## 6. Base e validação

- `geometry-of-numbers`: base `b711431f9393db9382739af19ea135d9bc11fc0f`.
- Operador consultado sem alteração:
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `momentos` não foi modificado. Nenhum experimento numérico foi usado como
  premissa das provas desta rodada.
- Pins, métricas, pesos, normalizações e estados anteriores preservados.

Os comandos e seus resultados finais são registrados em `validation.json`
e nos logs de evidência da entrega. A auditoria enumera separadamente os
48 novos roots públicos e verifica seus tipos e corpos transitivos com
`Lean.collectAxioms` e `#print axioms`. Foundation e Geometry conservam suas
políticas próprias; Analysis admite somente os três axiomas padrão.

Os oito checks passaram no servidor `llm`:

```bash
lake build --wfail GeometryOfNumbers.Analysis.CarryMaterialMixedSchur
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
lake env lean -DwarningAsError=true research/projective-global-return/Regression.lean
bash scripts/audit-material-projective-comparison.sh /home/thlinux/carry-self-adjoint-operator
bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator
```

O build completo considerou 8839 jobs. São 39 teoremas públicos e nove
definições novas auditadas. As regressões incluem ordens 2/4 independentes,
a parte imaginária depois da leitura complexa, os blocos de paridade,
a direção crítica e a distinção explícita da diagonal excluída. Os testes
anteriores de retorno, cutoffs independentes e conexão material passaram.

Os arquivos `new-roots.json`, `footprints.json`, `provenance.json` e os logs
comprimidos ficam em `research/material-mixed-schur/`, junto deste relatório.
