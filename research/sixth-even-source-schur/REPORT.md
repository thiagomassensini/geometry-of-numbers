# Sexta margem par da fonte Carry e certificado residual reutilizável

Estado: **PASS — sexto teste par certificado a partir da fonte theta original**, sem hipóteses novas. Os 19 módulos, 57 raízes públicas, build raiz `--wfail` (8841 jobs) e as três auditorias de zona passaram.

## Proveniência e escopo

Base `geometry-of-numbers`: `7e874fe8b6cfbec4463e5838a60cb359992b99b7`, merge do PR #28. Antes de editar: `main` limpo, remoto no mesmo SHA, PRs #25–#28 integrados e módulos correspondentes conferidos. Trabalho em `agent/sixth-even-source-schur`, no checkout principal; nenhuma worktree criada. As worktrees antigas foram preservadas.

Operador consultado: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Seus dois módulos C2 não rastreados foram preservados. `momentos`: `a54f267365d5d8c965376734b17b10ae89ed3f74`; diretório não rastreado `investigations/` preservado. Nenhum desses repositórios foi alterado.

Fontes, normalizações, fatores da característica, amplitudes, pesos, métrica, câmera, dressing, pins e módulos históricos estão inalterados. O certificado não recebe zeros, alturas, Jacobi, `raw_moments`, `f_coefficients` ou momentos escolhidos. A entrada Lean é exclusivamente a fonte theta infinita e a recorrência canônica preexistentes. Checkpoints servem apenas aos experimentos e à escolha de testemunhas não confiadas.

## A. Canários e decisão GO

Usados os CSVs `native_jet_exploration/auditoria_corrected_vs_canonical/stage_{A,B}/moments.csv`, somente coluna `canonical_h`. A auditoria histórica `SAME MOMENT SEQUENCE` foi lida com sua ressalva: identificação das definições acompanhada de teste numérico, sem nova prova Lean nem conclusão sobre operador infinito.

| Dados | Momentos / DPS salvos | SHA-256 do CSV integral |
|---|---:|---|
| Stage A | 64 / 500 | `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833` |
| Stage B | 256 / 2000 | `65c3ed4990c329229fe4c80152e6ddfc288d92787148d19ba75d163ee55ac793` |

`preflight.py` resolve os sistemas antigos por LU e QR/Householder, para n=1,…,5 em ambos os setores, usando 40,80,160,300 DPS sobre os MESMOS decimais. Não usa inversão numérica. Aumentar DPS não cria informação de entrada. A 40 DPS o QR recusa os casos n=5 como numericamente singulares; isso fica registrado. LU e QR a partir de 80 DPS, e os dois checkpoints, concordam nos 55 dígitos impressos dos canários.

| s,n | c | bᵀx | σ=c−bᵀx | σ/(abs(c)+Σ abs(bᵢxᵢ)) | Cancelamento |
|---|---:|---:|---:|---:|---:|
| 0,5 | 4.940256352281979e−26 | 4.940255939557815e−26 | 4.127241644034342e−33 | 2.026765530360626e−8 | 7.6932 dígitos |
| 1,5 | 2.472494444328769e−28 | 2.472494428599290e−28 | 1.572947964218230e−36 | 1.417927074342710e−9 | 8.8483 dígitos |

Resíduos Ax−b são gravados componente a componente em `evidence/preflight.json`, tanto na aritmética do solve quanto reavaliados a 400 DPS para evitar zeros artificiais por arredondamento. No solve de 80 DPS, as normas infinito reavaliadas são aproximadamente 3.2514e−96 e 6.4224e−98. Diferenças de pivô entre LU/QR: aproximadamente 1.5726e−107 e 2.3830e−109. Esses resultados continuam sendo experimentais.

Na normalização SOMENTE diagnóstica c0=1, o arquivo histórico `stage_A/coefficients.json`, chave `normalized_completed_c`, fornece c11≈−1.52714601028634761181e−27. A recorrência e o solve dão C≈−1.52714563508256179051e−27, diferença≈3.75203785821303819804e−34; onze vezes a diferença recupera σ. SHA do arquivo histórico integral: `ab31ac45968c054733965795f48b91997d11b269e345c88f2cfa145b8ce3254d`. A característica formal não foi normalizada por essa convenção.

**GO antes da codificação Lean:** o espelho inteiro das caixas EXISTENTES, com testemunhas mais estreitas para cada integral, deu I22 em

    [1.0279908351418508011213698327084e−9,
     1.0279908351418546461033707923302e−9],

largura 3.8449820009596217e−24. A propagação completa previu o sexto pivô ordenado em [4.0773867887964e−33,4.1613871177025e−33], largura 8.4000328906068e−35. Era suficiente para atacar o sinal sem recuperar momentos, aumentar modos ou refazer quadratura com novos parâmetros. A precisão exigida é a de uma caixa que preserve o endpoint inferior positivo; não um número de DPS arbitrariamente maior.

## B. Certificado da fonte original

`ThetaTwentyTwo.lean` estende a inclusão analítica até p=22 usando `mem_exactFullModeBox`, `integral_weightedOmittedModes_bounds` e a mesma identidade de soma da fonte. Conserva grau de Taylor 15, grid 64, três modos retidos e cutoffs 96/64,64/64,48/64. `GeneralTails`/`ModeSchedule` foram auditados; não foi necessário ampliar sua escolha de modos ou cutoffs nesta ordem.

Cada caixa de I0,I2,…,I22 é conferida em um arquivo `ThetaCheck*.lean` por `decide +kernel`. Os inteiros são testemunhas: o kernel verifica sua inclusão a partir do programa de quadratura certificado. Não são decimais do checkpoint admitidos como premissas. O arredondamento inteiro continua em escala 10^60.

Todos os erros permanecem: largura dos coeficientes exponenciais/pi certificados; resto Taylor de ordem 16 em cada célula; integral até infinito de CADA modo retido; TODOS os infinitos modos omitidos. Para p=22, as contribuições dominantes à largura são cerca de 3.7324e−24 do resto Taylor do modo 0 e 1.1248e−25 de sua cauda retida; a incerteza dos coeficientes desse modo é cerca de 8.0859e−29. O resto omitido tem upper bound menor que 3.6570e−45. O JSON de preflight registra os limites inteiros completos; as provas analíticas históricas justificam cada componente.

`SourceEnclosures.lean` aplica essas caixas à MESMA característica original e à MESMA recorrência da derivada logarítmica. Sua eliminação intervalar usa o kernel genérico `K(i,j)=h(i+j)` da Hankel original e conserva todos os acoplamentos, incluindo ocorrências repetidas das entradas. O nome histórico `carryMaterialEvenPairing` designa outro estágio, já centralizado; ele não foi confundido com essa Hankel na prova final. Não há fit nem redefinição do Gram. A eliminação ordenada é usada downstream da síntese e da recorrência, como teste finito de positividade. Sua fatoração serve à inferência de PosDef a partir de pivôs certificados; não constrói vetores físicos pelo Gram-alvo. As identidades de síntese e polarização anteriores conservam GG/GR/RG/RR e os canais Jordan positivo/negativo; nenhuma dessas portas foi alterada.

Resultados públicos principais no namespace `CarrySixthEven`:

- `sixth_ordered_even_pivot_bounds`: 4/10^33 < pivô ordenado 5 < 42/10^34.
- `even_source_six_posDef`: `(sourceMomentMatrix h 0 6).PosDef`.
- `sixth_even_pivot_pos`: `0 < sourceMomentSchur h 0 5`.
- `sixth_even_sourceThetaGap_pos`: `0 < sourceThetaGap 0 5`.
- `sixth_even_literal_theta_gate` e `sixth_even_integral_gate`: a desigualdade pedida, com J10=1848 I20−I22 e teto completo.
- `sixth_even_criticalMargin` e `sixth_even_eventually_above_pivot`: margem persistente no balanço físico ORIGINAL da direção crítica, via `criticalMargin_iff_pivot`.

O transporte usa `sourceMomentMatrix_succ_posDef_iff`, o prefixo H5 já certificado e as equivalências theta/físicas existentes. Não confunde a positividade isolada de J10 com a desigualdade do teto. O intervalo quantitativo acima é explicitamente do pivô ORDENADO; para o Schur por inverso e para a margem física afirmamos o sinal estrito transportado.

Não se conclui positividade ímpar 6×6, contratividade de TODO o retorno de doze fontes, realização física de doze jets ou limite de operador.

## C. Testemunho racional recebido e ferramenta geral

O script recebido foi reproduzido SEM alteração sobre o CSV completo Stage A. Seleciona o mesmo vetor racional de 20 algarismos e dá q≈4.12724164403434201784e−33 e limite inferior≈4.127241638241664459848e−33, correção relativa≈1.403522753838532e−9. O output recebido usava um CSV reduzido de SHA diferente; não se confunde esse hash com o CSV integral. Cópia do verificador: `checkpoint_rational_witness.py`; resultado reproduzido: `evidence/rational-witness-reproduced.json`. Seu SHA é `c8d203e09f08e84cc39f49983375ead6dac16293f662ff04e0e71f7c61b1def9`.

Esse cálculo `Fraction`, incluindo solves exatos do prefixo para limitar seu inverso, certifica somente racionais decimais. A suficiência perturbativa de erro relativo uniforme 10^−25 também é teste racional condicional; não foi promovida a prova de inclusão theta. As caixas atuais não atingem essa tolerância uniforme, mas a rota direta conserva sinal positivo com seus erros reais; logo não se impôs esse limiar como obrigação artificial.

`VariationalSchur.lean`, namespace `CarryVariationalSchur`, prova para qualquer ordem e vetor tentativa z, sem assumir o novo sinal:

    r=b−Az, E(z)=c−2bᵀz+zᵀAz,
    σ=E(z)−rᵀA⁻¹r.

A identidade exige somente invertibilidade do prefixo. As duas convenções b−Az e Az−b têm o mesmo erro quadrático, com teoremas explícitos. Um bound quadrático do inverso fornece σ≥E(z)−M(rᵀr); uma coerção α>0 do prefixo antigo fornece M=1/α e o critério sem divisão rᵀr<α E(z). As raízes principais são `sourceTrialEnergy_eq_schur_add_residual_of_isUnit`, `sourceMomentSchur_lower_bound_of_solveResidual`, `inverseResidual_bound`, `sourceMomentSchur_pos_of_trialResidual` e `sourceThetaGap_pos_of_trialResidual`. O bound M é enunciado diretamente como bound quadrático; não se apresenta uma prova adicional de perturbação espectral das matrizes do checkpoint.

Esses lemas são novos verificadores algébricos, não uma nova desigualdade física all-order. A auditoria também reutilizou a direção crítica total e a integral polinomial já existentes no operador; não as apresentou como novidades. O no-go da densidade ímpar como quadrado ponto a ponto se restringe àquela densidade. `structural-note.md` registra os nomes exatos e o gate restante: obter da fonte física um controle independente que satisfaça o critério residual em todas as ordens, preservando a alternância dos setores e todos os cruzamentos.

Whitening/Parseval Green e ortogonalização Hankel continuam distintos; nenhum intertwiner físico novo foi postulado. Controle absoluto das caudas, precisão de quadratura, sinal de Schur, contratividade, realização física e limite de operador permanecem afirmações separadas.

## Validação e reprodução

As dependências históricas compiladas são reutilizadas após verificar commits, pins comuns e todos os hashes dos manifestos históricos. Não se afirma reconstrução fresca dessas dependências. Todos os módulos novos são compilados com `warningAsError=true`; os checks inteiros usam `decide +kernel`, sem `native_decide`.

Reprodução formal no llm:

    bash research/sixth-even-source-schur/audit-sixth-even-source-schur.sh

O script compila os 19 módulos novos, confere o inventário público e audita transitivamente tipos E corpos com `#assert_central_comparison_axioms` e `#print axioms`; depois executa `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. A política Analysis permite somente `propext`, `Classical.choice`, `Quot.sound`; nenhuma hipótese numérica, novo axioma ou escape de confiança é aceito. A Foundation não foi alterada.

Logs, SHA dos arquivos e resultados ficam em `evidence/`. O build raiz sozinho não inclui automaticamente os arquivos de pesquisa: por isso a compilação explícita deles é indispensável. A redução das caixas é sequencial para limitar memória; não se geraram milhares de momentos.

Experimentos numéricos foram repetidos no llm com `/home/thlinux/miniforge3/bin/python3` (Python 3.12.12, mpmath 1.3.0), após o pré-teste local com a mesma biblioteca. Para reproduzir `preflight.py`, forneça `--checkpoint-root` apontando para a auditoria histórica, `--source-root` para `research/material-integral-certificate`, `--normalized-coefficients` para um JSON com a chave `values` contendo apenas `normalized_completed_c` do arquivo histórico, e `--output`. O script nunca usa as outras chaves históricas. Os hashes de entrada ficam na saída.

Publicação: PR descritivo após validação, sem merge automático nesta entrega. O SHA do commit da tarefa e o link do PR são registrados na mensagem de entrega; o manifesto conserva o base commit e os hashes exatos dos módulos validados.
