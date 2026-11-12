# Checkpoint — certificação cofactorial C3

- Fase atual: Checkpoint 2 concluído; próximo foco é auditar caixas da fonte até `c₆`.
- Repositório: `thiagomassensini/geometry-of-numbers`; worktree `/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112`.
- Branch `agent/c3-cofactor-chiral-certification-20261112`, base `origin/main` `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`; PRs #316/#317 confirmadas.
- Pins: Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Árvore original preservada; trabalho somente na branch isolada. Cache Lean é ignorado por `.gitignore` local.
- Commits publicados: `8c4287e` reconhecimento; `005f344` identidade cofactorial 3×3.
- Arquivos novos: `CofactorIdentity.lean`, `SchurGate.lean`, `C3Regression.lean`, `.gitignore`.
- Resultados: identidade do determinante e do vetor cofactorial 3×3, incluindo prefixo singular; critério condicional de PosDef via completar quadrados, sem inversa matricial.
- Teorema de gate: `odd_third_posDef_of_cofactor_gate`; hipóteses incluem explicitamente `a>0`, `D>0` e margem cofactorial estrita.
- Canários passaram: gate positivo; margem negativa rejeitada; prefixo singular na identidade; direção racional não crítica; controle sintético `1-u-u²` reutilizado de `CarrySourceBezout.regression_negative_control`.
- Observação: a identidade cofactorial vale para qualquer direção `u`; logo escolher a direção racional não altera o sinal exato, podendo ajudar somente no condicionamento intervalar.
- Validação Lean com `-DwarningAsError=true` passou para os três módulos novos; axiomas dos teoremas públicos: `propext`, `Classical.choice`, `Quot.sound`.
- Commit atual antes deste checkpoint: `005f344`; próxima alteração será commitada separadamente.
- Limitação: a prova geral para dimensão arbitrária ainda está aberta; nenhum coeficiente C3 da fonte foi certificado nesta branch.
- Próximo passo exato: integrar as caixas certificadas existentes e identificar o cálculo mínimo para estendê-las até `c₆`, sem importar sinal theta do pivô.
- Obrigações em aberto: identidade abstrata para todo `n`, caixas C3 até `c₆`, margem independente, C3/48 opcional, transporte quiral de ordem 11.
