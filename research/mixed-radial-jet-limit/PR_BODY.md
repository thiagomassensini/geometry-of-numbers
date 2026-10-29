A convergência diagonal dos jets físicos não permite identificá-los entre regularizações. Esta PR calcula o pareamento original com dois índices independentes: `Q(k,k) → h₀`, enquanto `Q(k,2k+1) → (3√2/4)h₀`. O fator vem do produto interno Cauchy original e não desaparece na síntese completada.

A diferença dos dois jets tem balanço assinado negativo eventualmente. Assim, não existe limite conjunto bruto nem uma única Gram Hilbert positiva que realize todos esses pareamentos sem transporte. O NO-GO é específico dessa união radial, não da geometria nem dos momentos canônicos.

A nota sobre potências primas também foi testada: suas fórmulas para `m₁,m₂` impõem `m₂≥m₁/2`; as caixas originais dão `h₂<h₁/16`. Um teorema exclui a identificação literal, mesmo com massa global positiva.

- 25 teoremas novos; 28 raízes auditadas em quatro camadas, com 5.572 dependências de tipos/corpos e somente axiomas fundacionais permitidos.
- 15 verificações com saída zero: módulos explícitos, fontes originais, `lake build --wfail` e auditorias Foundation/Geometry/Analysis.
- Fonte, métrica, duas quadraturas, canais, completion e cruzamentos preservados. Sem axiomas novos ou escapes de confiança.
- Base: PR #79, commit `8a287232a55709fb79847033143978f555fa10b4`. PR #41 permanece independente e é usada como contexto da obrigação assinada, não como import implícito.

**PARTIAL.** Próximo alvo: derivar do Green/TFVD original um transporte vetorial que explique o defeito `(ρ−1)K`, antes dos jets superiores. Relatório português A–E, comandos e evidências em `research/mixed-radial-jet-limit/`. Draft, sem merge automático.
