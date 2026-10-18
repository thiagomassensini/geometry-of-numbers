# Sétimo Schur par theta por avaliação centrada da mesma fonte

## Resultado e escopo

**Frente A: PASS.** Lean prova a positividade da Hankel original H7, de `sourceMomentSchur h 0 6`, do gap theta completo e da margem física persistente na direção crítica. A desigualdade literal certificada é

    -4 * 26! * sourceCeiling 0 6 < 2600 * I24 - I26.

**Frente B: identidade nova PASS; sinal all-order em aberto.** Foi formalizada uma recorrência exata para avaliação centrada com primeira variação e resto não linear. Ela resolve a perda de dependências neste teste finito. Foi formalizado também um critério residual relativo, condicional, e um contraexemplo à inferência de sinal por erro absoluto isolado. Não foi obtida uma estimativa da síntese física que prove a margem em todas as ordens.

Não há certificado de K7 ou de contratividade/realização de quatorze fontes. A realização completa de doze fontes dos PRs #29/#31 continua disponível, sem alteração. O resultado novo é um setor real 7×7 e sua direção crítica física.

## Base e fonte preservadas

Tarefa: [Issue #32](https://github.com/thiagomassensini/geometry-of-numbers/issues/32). Branch `agent/seventh-even-centered-source`, criada do `main` atualizado em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, após PR #33. Essa base contém o merge obrigatório do PR #31, `1490fd59fc9c96b3923e14bbb079e00d33ea85bd`. Checkout inicialmente limpo. Nenhuma worktree criada.

Operador somente lido: `/home/thlinux/carry-self-adjoint-operator`, HEAD `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Checkpoints somente lidos: `/home/thlinux/momentos`, HEAD `a54f267365d5d8c965376734b17b10ae89ed3f74`. Trabalhos locais desses repositórios preservados. Lean `v4.32.0`, mesmos pins mathlib/GreenFrame. O verificador confere os manifestos históricos e restringe o diff inteiro à pasta nova `research/seventh-even-centered-source/`.

Fonte, pesos, amplitudes, câmera, métrica, normalizações, dressing, fatores da característica e módulos históricos permanecem intactos. A sequência é a característica completada Carry e sua derivada logarítmica canônica, com coeficiente original c0 próximo de 0,49712. Nenhum decimal de checkpoint, zero, altura, Jacobi ou Gram-alvo é premissa do certificado Lean. As referências racionais são centros de expansão; sua distância da fonte verdadeira é incluída na prova.

## Pré-teste antes da formalização

`evidence/preflight.json` guarda os solves LU/QR dos dois setores, tamanhos antigos e próximo teste, em 40/80/160/300 DPS. Somente `canonical_h` foi lido. As precisões de 500/2000 DPS são as declaradas nos checkpoints Stage A/B; elevar a aritmética não acrescenta dígitos à entrada. SHA-256 dos CSVs:

| Entrada | SHA-256 |
|---|---|
| Stage A/moments.csv | `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833` |
| Stage B/moments.csv | `65c3ed4990c329229fe4c80152e6ddfc288d92787148d19ba75d163ee55ac793` |

Sétimo par, nos dois checkpoints, a 80/160/300 DPS:

    c = 1,2374934443249966331504138343350314281e-30
    bᵀx = 1,2374934438113102054920414548012676249e-30
    sigma = 5,1368642765837237953376380319047940e-40
    sigma/(|c|+sum |b_i*x_i|) = 8,647899327414428e-11
    cancelamento = 10,0630893748 algarismos.

A 80 DPS, a diferença de Schur LU–QR é aproximadamente 6,88e-112. O resíduo do solve, reavaliado em maior precisão contra os decimais originais, tem norma infinita 6,31e-98; a 160/300 DPS fica em 6,96e-178/1,73e-318. O QR a 40 DPS acusa singularidade numérica e é registrado como tal; não foi transformado em evidência favorável. O LU a 40 DPS concorda no sinal. As entradas individuais, resíduos e falhas estão no JSON.

Na normalização SOMENTE diagnóstica c0=1, c13≈−1,992696155116296e-33 e C(0,6)≈−1,992696115601955e-33; 13*(C−c13) reproduz o canário. Esses coeficientes vêm do arquivo diagnóstico preservado e NÃO alimentam Lean. O canário ímpar adicional no JSON também não constitui prova de K7.

### GO/STOP por rota de intervalos

O programa inteiro de caixas usa escala 10^60. As caixas Python são um pré-teste conservador das fórmulas; a aceitação final é feita pelo kernel Lean.

| Rota | Intervalo/erro observado | Decisão |
|---|---|---|
| Recorrência direta para h12 | largura 1,98165111352e-38 | insuficiente frente ao pivô ≈5,14e-40 |
| Eliminação original, caixas diretas | [−2,45255e-28; 5,77910e-35] | STOP desta avaliação |
| Mesma congruência P7, caixas diretas | último pivô [−174,108; 184,382] | STOP desta avaliação |
| Recorrência centrada para h12 | largura 8,13078605603e-43, com padding | GO |
| P7, caixas centradas | último pivô transformado [5,0917265; 5,1820021] | GO; Lean prova 5 < pivô < 53/10 |

Nenhum STOP de avaliação é uma prova de sinal negativo. O ganho de aproximadamente 24.372 vezes na largura de h12 veio da propagação algébrica das mesmas caixas de coeficientes, sem alterar grau, grade, cutoffs ou precisão da quadratura.

## I26, coeficiente c13 e erros mantidos

`SourceTwentySix.lean` estende o argumento analítico existente de p≤24 a p≤26. Mantém três modos retidos, Taylor de grau 15, grade 1/64 e 96/64, 64/64, 48/64 como limites respectivos. Cada modo inclui sua cauda após o cutoff. O termo dos infinitos modos omitidos permanece explicitamente limitado por p!/(10^20*95^(p+1)).

O kernel verifica a inclusão

    I26 ∈ [392276362639506979694180129641929731806884269735606,
           392276362639511895365195295091963405955158434926666] / 10^60.

Sua largura é 4,91567101516546e-24. Principais parcelas da largura: resto Taylor do primeiro modo 4,33220111745043e-24; cauda retida desse modo 5,83433866376851e-25; arredondamento de coeficientes desse modo 3,60311633565132e-29. A contribuição superior dos modos omitidos é 1,6109486009496e-47. As parcelas dos outros modos estão no JSON; nenhuma é descartada na prova.

`SourceCoefficients.source_c13_theta` prova c13=−(2600*I24−I26)/(4*26!) na normalização original. Com a caixa I24 reutilizada do PR #31, cuja largura é aproximadamente 4,21103e-24, obtém caixa c13 de largura aproximadamente 6,79012e-48. O orçamento é (2600*largura(I24)+largura(I26))/(4*26!), mais arredondamentos externos. A propagação direta amplificava essa incerteza na recorrência; o gargalo não exigiu nova integração.

## Avaliação centrada e certificado finito

`CarryCenteredRecurrence.centered_recurrence_identity` vale para qualquer ordem e coeficientes de referência C, momentos H e primeira variação L que satisfaçam as três recorrências explicitadas. Escrevendo U=m−H−L e δc=c−C, prova exatamente

    c0*U_n = −sum_(k<n) U_k*c_(n−k) − sum_(k≤n) L_k*δc_(n−k).

Não supõe positividade, não omite o produto não linear L*δc e não pressupõe o novo pivô. As referências deste teste são os pontos médios racionais das caixas de coeficientes. H e a matriz de derivadas são testemunhas racionais: `reference_recurrence_check` e `derivative_recurrence_check` conferem todas as recorrências por `decide +kernel`. Não são momentos físicos substitutos.

`CenteredEvaluation` prova a identidade para a sequência canônica original e, por indução, a inclusão do resto não linear. Caixas compactas de U e h são caches com inclusão conferida pelo kernel, não hipóteses novas. As caixas de U recebem padding 10^−54; as compactas de h, padding 10^−52, para acomodar arredondamentos externos de fórmulas de coeficientes equivalentes. O resto h12 da avaliação Python antes do padding é aproximadamente ±1,686e-57; a prova usa o cache mais largo. Os 13 momentos continuam derivados dos 14 coeficientes originais. A caixa compacta final de h12 é aproximadamente

    [1,237493444324590108381446016829e-30;
     1,237493444325403186987048097230e-30].

P7 é triangular superior racional, com diagonal [10,10^4,10^7,10^10,10^13,10^16,10^20]. A coluna j é escolhida por solve apenas do prefixo j e seus cruzamentos, arredondado a 40 algarismos significativos. A última coluna usa h0…h11, sem h12. Esses dados de checkpoint escolhem apenas um mapa de teste arbitrário; a prova aceita o mapa porque verifica a fonte verdadeira e a igualdade exata da forma.

`trialMatrix_identity` prova G=PᵀH7P, `trialMatrix_det_pos` prova sua invertibilidade, `trial_seven_rectangle_check` verifica os sete pivôs intervalares e `even_source_seven_posDef` transporta a positividade de volta. Todos os 49 pareamentos e suas somas completas são preservados. P não altera fonte, métrica ou vetores físicos. Sua escala elevada não é uma isometria física e não fornece controle uniforme ao crescer a ordem.

Raízes principais no namespace `CarrySeventhEven`:

- `even_source_seven_posDef`, `seventh_even_pivot_pos`.
- `seventh_ordered_even_pivot_pos`: sinal na ordem original da Hankel bruta h(i+j), usando a extração genérica do PR #31. Não confunde essa Hankel com um pairing Green centrado.
- `seventh_even_criticalMargin`, `seventh_even_sourceThetaGap_pos`.
- `seventh_even_literal_theta_gate`, `seventh_even_integral_gate`.
- `seventh_even_balance_limit`, `seventh_even_eventually_above_pivot`, `seventh_even_jordan_margin`, `seventh_even_sourceRemainder_pos`.

O intervalo 5…53/10 refere-se SOMENTE ao pivô transformado. O valor ≈5,13686e-40 é SOMENTE canário do pivô original; a conclusão Lean anunciada para ele é seu sinal estrito.

## Transporte físico e frente all-order

O limite do balanço físico crítico é 2*sigma(0,6), com H6 positivo já conhecido. O balanço fica eventualmente acima do próprio pivô positivo. `seventh_even_jordan_margin` expressa a dominação estrita do canal positivo sobre o negativo, mantendo os dois canais na direção crítica. A interface dessa direção usa o carrier de dimensão 14; isso não certifica todas as direções dessa face, seu retorno ou uma família física de 14 jets. Para isso K7 ainda é necessário. GG/GR/RG/RR, cruzamentos antigos–novos e síntese completa permanecem nas interfaces históricas, que não foram alteradas. Não é afirmado um intertwiner novo entre whitening Green e ortogonalização Hankel.

A regra testada para P_n usa prefixos antigos; a lei centrada é reutilizável em qualquer ordem, sem bootstrap do próximo sinal. Porém ambos controlam uma avaliação, não criam positividade. O resultado novo `CarryRelativeResidual.schur_pos_of_relative_budget` exige coercividade antiga alpha_n>0, E_n(z_n)>0 e ||r_n||²≤eta_n*alpha_n*E_n(z_n), com eta_n<1. Reutiliza a identidade variacional do PR #29 sem assumir o novo pivô.

`absolute_closeness_opposite_signs` formaliza um contraexemplo algébrico separado: momentos iguais a 1 exceto m2=1±δ têm o mesmo prefixo [1], Schur ±δ e distância entre entradas ≤2δ, arbitrariamente pequena. Isso refuta a inferência universal de sinal por uma tolerância absoluta fixa; não é um contraexemplo Carry. A positividade do prefixo [1] é a identidade matricial explícita de `perturbed_old_prefix`.

Obstruções existentes reutilizadas, não novidades desta rodada: PR #31 exclui alpha>0 uniforme nas coordenadas brutas; PR #33 limita o erro absoluto do cutoff polarizado completo e compara seu orçamento à escala crítica que decai. Uma cota absoluta uniforme não fornece por si a margem relativa do próximo Schur após amplificação pelo inverso. A positividade isolada de J_d também não resolve o gate: setor par exige limite INFERIOR J_(2n)>−4*(4n+2)!*Ceiling(0,n), setor ímpar exige limite SUPERIOR J_(2n+1)<4*(4n+4)!*Ceiling(1,n), ambos com feedback antigo completo.

**STOP do sinal all-order:** ainda falta deduzir da fonte física, para cada ordem e ambas as paridades, um orçamento relativo/residual estrito com controle de alpha_n e da amplificação, ou uma desigualdade física independente equivalente. A recorrência centrada melhora a precisão finita, mas não demonstra que as margens verdadeiras serão positivas em todas as ordens. Não há passagem ao limite de operador neste PR.

## Validação e reprodução

Executar no llm:

    bash research/seventh-even-centered-source/audit-seventh-even-centered-source.sh

O runner compila explicitamente os 11 módulos novos com avisos como erros, audita as 81 raízes públicas transitivamente por TIPOS E CORPOS e `#print axioms`, executa `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. Analysis permite somente `propext`, `Classical.choice`, `Quot.sound`; as políticas mais estritas das outras zonas permanecem intactas. Sem `sorry`, `admit`, axiomas customizados, `unsafe` ou `native_decide`; reduções racionais por `decide +kernel`.

Dependências históricas compiladas são reutilizadas após verificação de fontes, manifestos, commits e pins; não se anuncia recompilação fresca dessas dependências. O build raiz não inclui automaticamente os módulos de pesquisa, por isso a compilação explícita é necessária.

`evidence/build-results.json` registra os 18 comandos exigidos, diretórios, duração e exit codes. `source-manifest.json` identifica as fontes/scripts/documentação validados; `validation.json` vincula os hashes dos dados e logs. O empacotamento exige todos os comandos com exit code zero e `verify_evidence.py` reconfere os hashes e axiomas. Logs raiz e das zonas são comprimidos deterministicamente.

Reproduzir o pré-teste com `/home/thlinux/miniforge3/bin/python3 preflight.py`, fornecendo `--checkpoint-root /home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical`, `--source-root ../material-integral-certificate`, `--normalized-coefficients evidence/normalized-coefficients.json`, `--output /tmp/seventh-preflight.json`, a partir da pasta da tarefa. Python 3.12.12, mpmath 1.3.0. O JSON contém testemunhas completas, referências, derivadas, caixas e hashes; nenhuma saída Python é confiada pelo kernel.

Publicação em PR descritivo, sem merge automático. O commit e o link são registrados na entrega. Somente a pasta nova pertence ao diff; arquivos históricos, pins e trabalhos alheios são preservados.
