# Sexta direção ímpar: limiar radial explícito e curvatura da fonte completada

**Classificação: PARTIAL.** Para a sexta direção ímpar, a margem física da PR #138 agora tem um limiar radial inteiro explícito. Em todas as ordens, a resposta completada original fornece a identidade de curvatura dos momentos e da forma polarizada. A positividade canônica em todas as ordens continua aberta.

## A — O que já estava demonstrado

Base: `geometry-of-numbers` `ef5ee79e3eb597e23e77421620151f11f66d2574`, cabeça da PR #138, empilhada sobre #137, #136, #135 e #134. O operador original está no commit `bfeb10fd2425400fa38139903d12bf0599f02e53`. A PR #138 fornece o bloco antigo positivo e invertível, uma direção racional experimental, a cota \(r^TA^{-1}r\le10^{-38}\), todos os 36 pares da fonte e o critério relativo da âncora; seu limiar era apenas eventual. As caixas theta são certificações das entradas originais; não se reivindica uma prova exclusivamente geométrica de seu sinal.

A PR #41 fornece a identidade que liga a direção crítica original ao complemento de Schur sem pressupor o sinal do novo pivô. Os teoremas originais da característica completada e da resposta Green/TFVD fornecem a proveniência da sequência canônica. O certificado histórico já estabelece H6 e K6 na ordem original e a realização física de 12 fontes; os novos resultados não são uma extensão all-order dessa realização.

## B — Limiar racional para a fonte física

`CriticalCoefficient.lean` prova que cada um dos seis coeficientes da direção crítica original tem módulo no máximo 2, por congruência invertível e coercividade do prefixo, sem usar o sinal do sexto pivô. `RadialPairs.lean` conserva os 36 pares ordenados e prova que suas constantes estão abaixo de \(10^{12}\). As somas completas das constantes são limitadas por \(36\cdot10^{12}\) para a testemunha e \(144\cdot10^{12}\) para a direção crítica.

`RadialCutoff.lean` define

\[
 k_0=10^{28}-1.
\]

Para todo \(k\ge k_0\), as cotas Lean para os erros radiais completos satisfazem \(E_k(c)\le10^{-42}\) e \(E_k(c_*)\le2\cdot10^{-42}\). Também obtivemos

\[
 D_k(c)>9\cdot10^{-37},\qquad D_k(c_*)>8\cdot10^{-37},
\]
\[
 r^TA^{-1}r+E_k(c)+2E_k(c_*)<\tfrac1{50}D_k(c),\qquad E_k(c_*)<D_k(c_*).
\]

Os teoremas respectivos são `trial_error_after_cutoff`, `critical_error_after_cutoff`, `trial_source_lower_after_cutoff`, `critical_source_lower_after_cutoff`, `relative_budget_after_cutoff` e `critical_anchor_after_cutoff`. O número \(k_0\) é um limiar suficiente e conservador, não o menor índice nem um cálculo executado até ele. Os 2% controlam o orçamento relativo à energia da testemunha; não são uma contração uniforme das energias incidente e retornada. Isso certifica a direção finita já investigada, não uma lei de sinais em outras ordens.

## C — Fonte sigma, momentos e curvatura completa

A fonte é a característica completada **original** avaliada em `displacedHeight d t = t - i d`; sua coordenada espectral é \(\sigma=1/2+d\). Depois de avaliada a síntese completa, definimos sua densidade como o quadrado da norma e o jato logarítmico real como

\[
 h_n(d)=-\frac{n+1}{2(2n+2)!}\left.\partial_t^{2n+2}\log\|F(t-id)\|^2\right|_{t=0}.
\]

`displaced_log_jet_eq_green` identifica esse jato, em qualquer ponto onde a característica é analítica e não nula, com as derivadas da resposta Green normalizada original. `sigma_log_jet_center_eq_canonical` prova **em toda ordem** que \(h_n(0)\) é exatamente o momento canônico original; usa a identidade Green/TFVD preexistente e não supõe positividade de Hankel. `sigma_log_jet_even` prova a paridade no intervalo de deslocamentos da faixa original. A analiticidade e a não anulação são demonstradas no centro; fora dele são hipóteses locais explícitas, não uma afirmação de ausência global de zeros.

Sem receber a hipótese abstrata `Hharm`, `sigma_log_jet_curvature_at` prova onde a fonte é analítica e não nula:

\[
 h_n''(d)=-2(n+1)(2n+3)h_{n+1}(d).
\]

Em particular, `sigma_log_jet_curvature_center` aplica a identidade incondicionalmente no centro, com o momento canônico do lado direito; `sigma_log_jet_deriv_center` prova que a primeira derivada central se anula. Esses fatos não dão por si só o sinal de qualquer pivô.

`SigmaQuadratic.lean` conserva todos os pares de um vetor finito \(v\), para qualquer setor \(s\), ordem \(N\) e coeficientes reais:

\[
 \left.\partial_d^2\sum_{i,j<N}v_iv_jh_{i+j+s}(d)\right|_{d=0}
 =-2\sum_{i,j<N}v_iv_j(i+j+s+1)(2i+2j+2s+3)h_{i+j+s+1}.
\]

Essa é `sigma_moment_form_curvature_center`. `sigma_critical_form_center_eq_schur` identifica o valor da mesma forma na direção crítica canônica com o Schur, assumindo apenas a inversibilidade do bloco antigo. `sigma_critical_form_curvature_center` aplica a fórmula à direção crítica **mantida fixa no centro**. Não se afirma ainda a igualdade dessa derivada com a derivada do pivô cuja direção varia com \(d\).

## D — Auditoria, limites e reprodução

Os módulos novos de pesquisa são independentes dos arquivos históricos. `validate.sh` os compila explicitamente com avisos como erros, executa `Audit.lean` e `lake build --wfail`. A auditoria transitiva percorreu 65.734 dependências de 10 raízes e bloqueia teoremas anteriores de positividade do sexto pivô/bloco ampliado como premissas, mas permite a positividade do prefixo antigo e as caixas da fonte. `#print axioms` foi executado para as declarações novas e encontrou somente `propext`, `Classical.choice` e `Quot.sound`. O build raiz com `--wfail` passou, com 8.849 tarefas. As auditorias separadas de Foundation, Geometry e Analysis também passaram; Foundation tem footprint vazio, Geometry e Analysis seguem suas políticas próprias. A comparação de 261 arquivos compilados reutilizados com a worktree anterior não encontrou divergências; isso confirma identidade dos objetos reutilizados, **não** uma reconstrução histórica limpa desde o código-fonte.

O trabalho usa Lean 4.32.0. No host `llm`, a partir da worktree desta investigação:

```bash
bash research/native-sixth-explicit-sigma/validate.sh
bash research/native-sixth-explicit-sigma/audit-layers.sh
python3 research/native-sixth-explicit-sigma/cache_manifest.py
```

Logs e manifesto são guardados em `evidence/`; os logs extensos da análise e do build raiz estão compactados em `.log.gz`. Não foram introduzidos novos axiomas, `sorry`, `admit` ou `native_decide`. A validação do código de pesquisa é separada do build raiz, que não o descobre automaticamente.

## E — Próximo passo mínimo

Transportar o lema de curvatura **do pivô móvel** de `momentos/lean/MomentosHankel/PivotSecondDerivative.lean` para uma vizinhança local do centro, usando a analiticidade da família de momentos, a inversibilidade local do prefixo e `SchurVectorSmoothness.lean`. Com a derivada central da matriz igual a zero, deve-se provar que os termos da direção crítica móvel se cancelam e que a segunda derivada do Schur coincide com a fórmula já provada para o vetor fixo. Essa passagem ainda precisa ser formalizada e não determina, por si só, o sinal do somatório com seus cruzamentos. A obrigação posterior é uma desigualdade independente da positividade do pivô, diretamente na fonte completa e com cauda controlada.
