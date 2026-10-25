A porta Mellin finita da PR #90 não tinha ainda um domínio de extensão identificado. Esta continuação prova duas propriedades distintas: ela é uma aplicação linear contínua na torre G_pre nativa já existente, mas não admite extensão linear fechada no carrier físico Cauchy L² isolado, mesmo preservando o trace como coordenada separada.

A obstrução usa fontes finitas originais G_n(u)=(n+1)sqrt(u)u(1-u)^n, todas com trace zero. Sua norma Cauchy tende a zero, enquanto o readout de qualquer primo fixo tende a 1; o fecho do gráfico contém (0,0) e (0,1). Na torre, os mesmos coeficientes têm norma pelo menos n+1. Portanto o resultado não descarta a norma vertical nem as isometrias Carry já existentes. Também não refuta a síntese na direção torre→Cauchy.

A comparação responde à pergunta sobre as verticais sem substituir métricas: a leitura tem controle positivo a montante, e os dados verticais não podem ser recuperados por um mapa limitado usando somente a norma Cauchy. Foram rechecados os axiomas das isometrias C2 e da identidade theta dos polinômios citada no novo contexto. A nota Jacobi permanece um controle do residual de Schur, sem transportar automaticamente o sinal à fonte.

**Resultado global: PARTIAL.** NO-GO local para a extensão isolada nessa topologia; controle vertical provado; kernel canônico all-order aberto. Próximo alvo: síntese direta dos estados verticais, com cota uniforme e todos os cruzamentos, seguida da comparação com o kernel completado efetivo.

Validação: 31 teoremas novos e 8 definições, 39 raízes públicas e 5624 dependências transitivas auditadas; 17 comandos aprovados, incluindo compilações explícitas com warningAsError, `lake build --wfail` e auditorias Foundation/Geometry/Analysis. Quatro módulos imutáveis da PR #90 foram recompilados. Sem novos axiomas, sorry, admit, native_decide, ajuste de fonte ou métrica. Logs e comandos em `research/mellin-physical-domain/evidence/`; relatório A–E em português em `REPORT.md`.

Base: PR #90, commit 457ea144d33d0b376a5c589b06ef1695e6d14adb. Somente nova pasta de pesquisa. Draft, sem merge automático; arquivos preexistentes e pins preservados.
