# C5 — estado da sessão

**Atualizado:** 2026-11-06  
**Status:** inventário inicial concluído; nenhuma prova C5 em Lean foi criada nesta branch.  
**Branch de trabalho:** `codex/c5-finite-c2-certification-20261106`, baseada em `origin/main`.  
**Main geometry:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776` (PR #164).  
**Repositório geometry no checkout de pesquisa original:** branch `agent/native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, com logs/caches não rastreados preservados.  
**Repositório Momentos:** checkout local `main` em `05c9314d59306383baa55ed3be80ab950e799e97`; branch remota de pesquisa `origin/research/sigma-pade-dimension-depth-20261104` em `68c9b5f` (verificar SHA integral no Git antes de retomar). PR #2 está OPEN e não foi integrada.

## Inventário de trabalho anterior

- C2, C3 e C4 constam integradas à main geometry. C4 está documentada em `mission-sigma-sign-20261105/evidence/c4-source-bezout/VALIDATION.md`.
- `SigmaSourceBezout.lean` já define `completedSigmaDisplacedSourceCoefficient` e `completedSigmaDisplacedMoment`; prova `C_d·H_d=-C_d′`, `H_d(n)=2*completedSigmaLogJet d n`, e `c₀>0` para os deslocamentos no domínio. O fator 2 deve permanecer explícito.
- Não foi encontrado módulo Lean C5 equivalente aos nomes `SigmaFiniteCoefficientSignTransport.lean`, `SigmaFiniteRationalSignCertificate.lean` ou aos teoremas `completedSigma_first_negative_window_at_*` nas branches/refs acessíveis.
- A branch remota Momentos já contém `c2_em_interval.py`, `certify_finite_c2.py`, `verify_signs_exact.py`, duas caixas racionais e relatórios. As caixas produzem sinais condicionais; os próprios relatórios afirmam que a correção das operações elementares de `mpmath.iv` e a inclusão dos coeficientes verdadeiros não foram formalizadas.
- O diretório `research/c3-fourteenth-tail/` e seus módulos dizem respeito a outro certificado finito; foram observados durante a busca, não serão reutilizados sem prova de correspondência à fonte C2 desta missão.
- Há várias worktrees com alterações/logs paralelos. A branch de pesquisa original e caches/logs não rastreados foram mantidos intactos; C5 usa worktree nova.

## O que está provado / condicional / pendente

**PROVADO e integrado (contexto):** C2 eventual em `d=1/5`; C3 setores par e ímpar; C4 recorrência original e equivalência Bézout. Isso não prova os sinais finitos desta missão em `d=99/2000` ou `d=1/10`.

**NUMÉRICO/INTERVALAR condicional:** as rotinas publicadas indicam `+++++++++++-` em `d=0.0495` e `+++++++++-` em `d=0.1`, supondo as caixas dos coeficientes.

**PENDENTE:** compilar o transporte algébrico em Lean; formalizar as contas racionais; demonstrar que os coeficientes da fonte original pertencem às caixas; compor os dois teoremas finais e auditar axiomas/build.

## Validações ainda não executadas nesta sessão

- Reexecutar as duas verificações por frações exatas sobre os JSON rastreados.
- Reexecutar as três configurações de geração intervalar (A, A independente com `L=12`, B) em diretório versionado de evidências.
- Investigar/certificar o backend das operações elementares e as hipóteses analíticas que transferem o contorno para a fonte C2.
- Compilar e auditar cada módulo Lean C5 em Lean 4.32.

## Regras de estado

Nenhuma caixa do JSON será elevada a fato sobre os coeficientes sem uma prova de inclusão. Se essa prova não for concluída, os teoremas serão explicitamente condicionais e o nível final será no máximo `PROVADO — TRANSPORTE ALGÉBRICO E CERTIFICADO CONDICIONAL` ou `PARCIAL — BLOQUEIO INTERVALAR DELIMITADO`.
