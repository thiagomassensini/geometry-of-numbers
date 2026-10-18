# Sexto pivô ímpar theta, K6 e retorno físico de doze fontes

Estado: **PASS nas etapas A, B e C**, desde a fonte theta original, sem hipóteses novas. Etapa D concluída com obstruções formais e o gate all-order explicitamente aberto. Validação integral PASS: 11 módulos novos, 78 raízes públicas, `lake build --wfail` com 8841 jobs e as três auditorias de zona.

## Escopo e proveniência

Tarefa: [issue #30](https://github.com/thiagomassensini/geometry-of-numbers/issues/30). Base exata `76fead5cbc40c350449966a5f5c89ff8ea47d234`, `main` após merge do PR #29. O checkout estava limpo; o remoto e o merge foram conferidos antes das edições. Branch nova: `agent/sixth-odd-twelve-sources`, no checkout principal do llm. Nenhuma worktree criada ou alheia alterada.

Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Os dois arquivos C2 não rastreados foram preservados. Checkpoints no `momentos`, HEAD `a54f267365d5d8c965376734b17b10ae89ed3f74`; diretório não rastreado `investigations/` preservado. Manifestos e pins das dependências históricas foram conferidos.

Nenhuma fonte, câmera, característica, fator de completamento, peso, amplitude, métrica, normalização ou pin mudou. Todos os arquivos da tarefa são novos em `research/sixth-odd-twelve-sources/`. A fonte continua sendo a característica completada Carry, sua identidade theta e a recorrência da derivada logarítmica. O certificado Lean não usa decimais de checkpoint, zeros, alturas, Jacobi ou momentos ajustados como premissas.

## A. Canários e pré-teste antes da redução Lean

Reutilizados SOMENTE os momentos `canonical_h` dos CSVs históricos:

| Stage | Momentos / DPS salvos | SHA-256 do CSV completo |
|---|---:|---|
| A | 64 / 500 | `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833` |
| B | 256 / 2000 | `65c3ed4990c329229fe4c80152e6ddfc288d92787148d19ba75d163ee55ac793` |

`preflight.py` reavalia ambos a 40,80,160,300 DPS por LU e QR, resolvendo Ax=b. A 40 DPS QR recusa o sexto teste como numericamente singular; esse resultado é preservado. A partir de 80 DPS, as duas rotas e os dois checkpoints concordam nos 55 dígitos impressos do canário ímpar:

    sigma ≈ 1.572947964218230132118755772837669557804260302171217517e−36
    c     ≈ 2.472494444328769346059036640923093085638858226727911141e−28
    bᵀx   ≈ 2.472494428599289703876735319735535357262162648685308119e−28

A razão sigma/(abs(c)+Σ abs(bᵢxᵢ)) é aproximadamente 1.417927074342710e−9: 8.84835 dígitos de cancelamento. A 80 DPS, a diferença LU/QR é aproximadamente 2.3830e−109 e a norma infinito de Ax−b reavaliada a 400 DPS é 6.4224e−98. Resíduos componente a componente e resultados de todas as precisões ficam em `evidence/preflight.json`. Aumentar DPS aqui não acrescenta dígitos à entrada armazenada.

Na convenção apenas diagnóstica c0=1, os coeficientes históricos da mesma característica dão c12≈1.83925984995880392526e−30 e teto≈1.83925998103780094344e−30. A diferença≈1.31078997018185844343e−37, multiplicada por 12, recupera o canário. A normalização FORMAL continua sendo a original: c0≈0.4971207781883141. Esse diagnóstico não entra no certificado.

**NO_GO para a propagação intervalar direta da eliminação original:** com as caixas theta atuais, o último intervalo é aproximadamente

    [−1.1669969803644e−31, 7.9998443630240e−34],

largura 1.1749968247274e−31. Ele cruza zero e não certifica sinal algum. Os cinco pivôs anteriores são positivos no pré-teste. O alargamento dominante aparece na realimentação das divisões intervalares, especialmente após o quinto pivô; não é uma nova evidência de pivô verdadeiro negativo.

**GO para avaliação em coordenadas racionais fixas:** tentativas obtidas por solves dos prefixos antigos, arredondadas a 30 algarismos, formam um mapa triangular invertível P. Sua diagonal é [10²,10⁵,10⁸,10¹¹,10¹⁵,10¹⁸]. Esses números são coordenadas de teste, não parâmetros físicos ou renormalização da fonte. A última tentativa usa A5 e b5 (até h10); h11 não é usado para escolher seus coeficientes. O cálculo propaga os MESMOS momentos intervalares em PᵀK6P. O sexto pivô transformado fica em [1.0371291421020,2.1087667868003], estritamente positivo. Não foi necessário apertar a fonte ou recalcular seus momentos.

P não é uma família de vetores físicos construída a posteriori. É uma mudança finita de coordenadas para verificar uma forma já definida. Sua igualdade com PᵀK6P e sua invertibilidade são provadas em Lean, e a positividade é transportada de volta à matriz original. Nenhum Gram-alvo é postulado como fonte física.

## B. Integral completa I24 e sinal da fonte

`OddSourceTwentyFour.lean` estende a inclusão analítica até p=24 e verifica a nova caixa por `decide +kernel`. A quadratura permanece: Taylor grau 15, grid 64, três modos retidos, cutoffs 96/64,64/64,48/64. `GeneralTails` e `ModeSchedule` foram inspecionados; não é necessário mudar sua escolha de modo/cutoff nesta ordem.

O intervalo certificado de I24 é:

    [6.1477367832354019889714177511330e−10,
     6.1477367832354440992551074288777e−10],

largura 4.2110283689678e−24. TODOS os erros permanecem: enclosures exponenciais/pi, resto Taylor de ordem 16 em cada célula, cauda infinita de CADA modo retido e infinitos modos omitidos. Para p=24, dominam cerca de 3.95482e−24 de resto Taylor e 2.56152e−25 de cauda do primeiro modo. Sua largura de coeficientes é cerca de 5.23535e−29; o majorante dos infinitos modos omitidos é menor que 2.23675e−46. O JSON registra os limites inteiros completos, derivados das estimativas analíticas existentes.

`OddSourceBoxes.lean` prova desde a fonte:

    c12 = (2208 I22 − I24)/(4·24!),

e a inclusão de h11 pela MESMA recorrência canônica com toda a soma antiga. As caixas h0,…,h10 são as do PR #29. Um cache compacto de h0,…,h11 é conferido por redução inteira; não é uma nova sequência. A largura de h11 é aproximadamente 6.08441e−37. O arredondamento inteiro conserva escala 10^60.

`OddTrialData.lean` contém apenas testemunhas racionais não confiadas e caixas verificadas. `OddTrialPositivity.lean` prova:

- `trialMatrix_identity`: igualdade exata com PᵀK6P, mantendo todos os cruzamentos.
- `trialMatrix_det_pos`: invertibilidade do mapa triangular, conferida sem supor K6>0.
- `trial_sixth_pivot_bounds`: 1 < pivô ordenado TRANSFORMADO < 22/10.
- `trial_six_posDef`, seguido de `odd_source_six_posDef`: positividade transportada à Hankel ORIGINAL K6.
- `sixth_odd_pivot_pos`: sinal de `sourceMomentSchur h 1 5`, usando o K5 já certificado.
- `sixth_odd_sourceThetaGap_pos` e `sixth_odd_criticalMargin`.

O intervalo [1,22/10] pertence exclusivamente ao pivô transformado; não é reportado como intervalo do pivô original ou do Schur por inverso.

`OrderedKernelPositivity.lean` prova uma extração genérica do sinal do pivô ordenado de uma matriz simétrica positiva, passando por seu Schur inicial e preservando o restante. `OddOrderedCertificate.sixth_ordered_odd_pivot_pos` aplica isso ao `carryMaterialOddPairing` ORIGINAL. Portanto o sinal do pivô ordenado original foi provado, sem reutilizar indevidamente a escala do intervalo transformado.

`Regression.sixth_odd_literal_theta_gate` e `sixth_odd_integral_gate` provam literalmente:

    J11 = 2208 I22 − I24 < 4·24!·sourceCeiling 1 5.

A prova usa a orientação ÍMPAR de `oddMargin_iff_upper_theta`, o `sourceCeiling` completo e as equivalências existentes. Não substitui essa diferença por J11>0. As raízes públicas usam somente os axiomas padrão de Analysis, conferidos transitivamente; nenhum axioma numérico foi acrescentado.

## C. Transporte físico de doze fontes

Só depois de K6>0, `OddPhysicalTwelve.lean` reúne K6 com o H6 do PR #29 através de `finiteBoundary_positive_iff_sectorMatrices 6`. Obtém a positividade da face complexa de 12 fontes e a margem uniforme EM DIREÇÃO, nessa dimensão fixa. Os teoremas físicos existentes fornecem:

- `twelve_boundary_positive`, `twelve_boundary_margin`.
- `twelve_return_eventually_contractive` e `return_contractive_through_twelve`: contratividade eventual do retorno original em dimensão 12 e seus prefixos.
- `correctedGreen_twelve_physical_realization`: doze vetores residuais no carrier Cauchy ORIGINAL e no espaço incidente físico `RadialIncidentSpan 0 12`.
- `canonical_twelve_physical_realization`: recomposição com o canal central já extraído, realizando TODOS os coeficientes polarizados canônicos dos jets 0…11.
- `canonical_twelve_nested_realization`: uma MESMA escolha realiza todos os pareamentos de todos os prefixos no carrier de doze.
- `ten_to_twelve_residual_crossings`: compatibilidade física exata das portas, eventualmente em k, para todo par do prefixo antigo.
- `correctedGreen_twelve_synthesis_pairing_tendsto`: entradas complexas arbitrárias e independentes são sintetizadas antes do pareamento; nenhum cruzamento de coeficientes é descartado.

Precisão de tipo: os vetores RESIDUAIS vivem no carrier Cauchy original. O jet completo `fullSourceJet` vive no produto Hilbertiano preexistente `FullSourceCarrier = WithLp 2 (ℂ × CauchyCarrier)`, que recompõe o canal central original. Não foi inventado um carrier ou ajustada uma métrica para esta ordem. A realização no limite usa os mecanismos físicos de compactação já construídos; não se anuncia convergência forte de todo o caminho radial quando a interface só fornece uma família física limite.

`OddPhysicalPolarization.lean` conserva os dois canais Jordan em `twelve_jordan_signed_pairing`. O negativo se anula EVENTUALMENTE apenas depois da contratividade provada, em `twelve_jordan_ports_eventually`; não é apagado por uma hipótese nova. `twelve_complete_source_comparison` reutiliza a síntese geométrica e sua discrepância assinada completa, sem supor que ela se anule ou tenha sinal favorável. Sua condição explícita de faixa geométrica é a da identidade existente.

`twelve_tfvd_synthesis_four_channels` registra a reconstrução TFVD upstream para superposições completas de doze estados ordinários: GG, GR, RG, RR permanecem. Esse teorema não é um intertwiner novo entre o frame Green e a Hankel. `twelve_block_calibration` confere o centro, ambas as diagonais novas h10/h11, cruzamentos antigos–novos nos dois setores e o cruzamento misto 10–11, em UMA família física.

São dois blocos reais 6×6 e uma face complexa de 12 fontes. Não se afirma uma Hankel real 12×12 positiva, um limite de operador infinito ou identidade automática entre whitening/Parseval Green e ortogonalização Hankel.

## D. Investigação da lei geral e obstruções novas

Reutilizado `CarryVariationalSchur`: r=b−Az, E(z)=c−2bᵀz+zᵀAz e sigma=E(z)−rᵀA⁻¹r. A condição suficiente sem divisão é rᵀr<alpha E(z), se alpha>0 e alpha‖y‖²≤yᵀAy para o prefixo antigo. O novo pivot não é premissa desses lemas.

`ResidualObstructions.lean` traz uma restrição da PRÓPRIA fonte, sem supor positividade global: qualquer coercividade alpha do bloco de tamanho n+1 satisfaz

    alpha ≤ h(2n+s) ≤ (22/175)^(n+1).

`native_coercivity_upper_bound` usa apenas teste de coordenada e o majorante incondicional existente dos momentos. `no_uniform_native_coercivity` conclui que não existe alpha>0 uniforme em toda ordem nas coordenadas ORIGINAIS dos momentos. Isso obriga uma eventual estratégia residual a controlar a dependência da ordem e a amplificação pelo inverso. Não exclui constantes alpha_n positivas dependentes de n ou coordenadas de verificação reescaladas.

Há também um contraexemplo FORMAL separado, `proxyMoments`, sem modificar a fonte: m_k=(1/2)^k, exceto m2 dividido por dois. Todos os momentos são positivos e geometricamente limitados, mas seu Schur de ordem 1 é −1/8. `positive_trial_energy_negative_schur` prova que a energia de tentativa E(0)=1/8 é positiva no mesmo exemplo. Logo positividade de entradas, controle de caudas/decadência ou E(z)>0 isolado não certificam o próximo sinal. Esse contraexemplo não satisfaz nem contradiz as identidades adicionais da fonte Carry: refuta somente essas estratégias algébricas ingênuas.

**Gate all-order ainda aberto:** obter de uma estimativa física/source-first independente, para cada ordem e setor, alpha_n>0 e z_n tais que a coerção antiga e ‖r_n‖²<alpha_n E_n(z_n) sejam demonstradas, controlando erros propagados por A⁻¹. Nenhuma desigualdade nova da síntese física que cumpra isso em TODAS as ordens foi obtida. A novidade all-order desta rodada é a obstrução rigorosa à coercividade uniforme e os contraexemplos, não uma solução da hierarquia.

## E. Validação, evidências e reprodução

Reprodução no llm:

    bash research/sixth-odd-twelve-sources/audit-sixth-odd-twelve-sources.sh

O runner compila explicitamente todos os 11 módulos novos com avisos como erros, audita as 78 raízes públicas por TIPOS E CORPOS com `#assert_central_comparison_axioms` e `#print axioms`, executa `lake build --wfail` e auditorias Foundation, Geometry e Analysis. A Foundation permanece intocada; Analysis permite somente `propext`, `Classical.choice`, `Quot.sound`. Não há `sorry`, `admit`, axioma customizado, `unsafe` ou `native_decide`. Checks racionais usam `decide +kernel`.

As dependências históricas compiladas são REUTILIZADAS após checagem de fontes, manifestos, commits e pins. Não se anuncia recompilação fresca dessas dependências. O build raiz sozinho não inclui automaticamente os arquivos de pesquisa; por isso a lista explícita é necessária.

`evidence/build-results.json` registra comandos, diretórios, duração e exit codes. `evidence/source-manifest.json` identifica os módulos/scripts/documentação efetivamente validados. `evidence/validation.json` contém hashes SHA de dados e logs; inclui a issue lida, os CSVs de origem no preflight, e as tabelas/testemunhas no hash das fontes Lean. O empacotamento só aceita todos os comandos exigidos com exit code zero. Os logs raiz e das zonas são comprimidos deterministicamente.

Pré-teste numérico: `/home/thlinux/miniforge3/bin/python3` no llm, Python 3.12.12 e mpmath 1.3.0. Invocar `preflight.py` com `--checkpoint-root /home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical`, `--source-root research/material-integral-certificate`, `--normalized-coefficients research/sixth-even-source-schur/evidence/normalized_completed_c.json`, `--output` para um novo arquivo. A característica normalizada é usada apenas no diagnóstico; as testemunhas Lean continuam verificadas da fonte original.

Publicação: PR descritivo após validação, sem merge automático. Base, commit da tarefa, link e estado final são registrados na mensagem de entrega e no PR. Nenhum arquivo histórico ou trabalho alheio foi incluído.
