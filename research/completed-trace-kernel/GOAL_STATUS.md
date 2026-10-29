# Auditoria de alcance do objetivo

O objetivo integral permanece ativo e não foi concluído.

1. O pareamento completado nativo/Mellin da PR #76 foi reutilizado por
   fontes reais recompiladas e agora identificado com os traços e o
   pareamento Cauchy das seis componentes físicas existentes.
2. A substituição do pareamento físico pelo bordo tem um residual exato,
   registrado em `boundary_minus_bulk_mellin`.
3. O cruzamento entre regularizações radiais tem o fator não trivial
   `crossRadialFactor`. A identificação sem esse fator falha num canário
   concreto já na primeira leitura; os estados envolvidos são distintos.
4. Uma Gram positiva única dos momentos canônicos, preservando todos os
   cruzamentos e a informação independente, não foi obtida.
5. Não foi provada positividade all-order de H ou K, independência de uma
   família física de todos os jets, nem removida a condição de sinal dos
   consumidores Jacobi/alturas.

As notas de Momentos foram verificadas numericamente e nos decimais
racionais. A reconstrução universal e a positividade canônica são
obrigações diferentes. O material não é usado como hipótese de sinal
das provas Lean desta etapa.

As PRs anteriores, a #41 e os arquivos preexistentes de todos os
checkouts foram preservados. Não se fez merge automático nem ajuste de
fonte, fase, amplitude, denominador, métrica ou pin.
