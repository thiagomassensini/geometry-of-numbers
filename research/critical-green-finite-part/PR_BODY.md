A PR #86 identificou a reconstrução vetorial e os nove cruzamentos da direção original `J₂−aJ₀`, mas só tinha o limite do balanço completo. Esta continuação demonstra sua expansão exata:

`Eₖ(a)=P(a)+κ⁻² C(a)+κ⁻⁴ Q(a)+O(κ⁻⁶)`, com `κ=k+1`.

Os coeficientes são `P=h₂−2ah₁+a²h₀`, `C=−a²h₁+40ah₂−14h₃` e `Q=a²h₂−462ah₃+147h₄`. O resto analítico é conservado na identidade e recebe uma estimativa eventual. A síntese completa, as pernas, a métrica, a fase, os nove cruzamentos, os bordos e o completion são preservados.

Na direção crítica `a=h₁/h₀`, o termo finito é o Schur original. Reutilizando explicitamente as duas desigualdades finitas da fonte já provadas na PR #43, obtém-se `C<0` e `0<Eₖ<p` eventualmente. A expansão analítica é auditada separadamente desses certificados. Não se afirma monotonicidade, cutoff explícito, sinal da correção quártica ou positividade all-order.

Validação: cinco módulos Lean novos e auditoria explícita com avisos como erros; `lake build --wfail` focado e raiz; auditorias Foundation/Geometry/Analysis; inspeção transitiva de tipos/corpos e `#print axioms`; diagnóstico 80/120 dígitos dos nove cruzamentos e da recomposição. Logs e hashes em `research/critical-green-finite-part/evidence/`, relatório em português em `REPORT.md`.

Base: PR #86, commit `beb07b54e7cffa767a33cc3e1f7d53018a2e9aca`. Resultado PARTIAL. As PRs #41/#43 são preservadas, com proveniência explícita dos certificados reutilizados. Draft, sem merge automático.
