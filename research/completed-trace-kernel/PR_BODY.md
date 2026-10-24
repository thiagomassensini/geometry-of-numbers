Os traços do núcleo físico da PR #78 precisavam ser comparados com o pareamento completado original sem substituírem o produto interno Cauchy. Esta PR identifica, em dois argumentos independentes e para cutoffs independentes, os traços das seis componentes originais, o wedge de Euler e o pareamento Cauchy com `completedIntegralPairing`. Calcula literalmente o residual entre bordo e interior, com todos os cruzamentos e completion preservados.

A comparação de regularizações diferentes produz um fator radial exato. Ele vale 1 na mesma grade, mas vale `2√2/3 < 1` para dois rótulos que têm o mesmo parâmetro espectral e endereços materiais diferentes. Os estados originais são distintos, com distância quadrática `(k+1)(1−2√2/3)`. O residual ao omitir o fator é estritamente não nulo num canário da fonte. Nenhuma métrica ou normalização foi ajustada.

**PARTIAL:** estes resultados não fornecem a Gram positiva canônica all-order. O teste histórico de fluxo de bordo negativo é reutilizado como compatibilidade do traço, sem ser apresentado como nova descoberta. A PR #41 permanece independente. O próximo cálculo é o limite polarizado dos jets com índices radiais independentes, preservando o fator e os estados materiais.

Também foi verificada a publicação de Momentos `0d0dd09`: replay N8/100 DPS com erro máximo `1.6711435e-99` e checagem independente em `Fraction` dos decimais, via soluções Hankel diretas. Isso valida as identidades finitas de reconstrução e entrada de níveis; não certifica integrais nem positividade all-order. Nenhum arquivo de Momentos foi alterado e nenhum dado numérico foi usado como hipótese Lean.

Base: `agent/physical-cauchy-endpoint-domain`, commit `4f98f0343b596f3c133d42dfb1ea3055fa069664` (PR #78). Draft empilhada, sem merge automático.

Validação: 30 módulos ancestrais reais recompilados; 40 teoremas e 15 definições novas; 55 raízes e 5.622 dependências de tipos/corpos auditadas. Quatorze comandos de validação com saída zero, builds `--wfail`, auditorias Foundation/Geometry/Analysis e guardas de fonte/sinal. Verificação de Momentos separada e reproduzível. Relatório A–E e evidências em `research/completed-trace-kernel/REPORT.md`.
