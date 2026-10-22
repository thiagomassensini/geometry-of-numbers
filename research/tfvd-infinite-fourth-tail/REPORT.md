# TFVD infinito: resto de quarta diferença e orçamento crítico cúbico

**Resultado: PARTIAL — a obrigação local de aceleração infinita foi fechada.**
O resto e os bordos da PR #59 agora têm estimativas provadas na fonte original.
As caudas dos dois canais passam de ordem M^(-1) para M^(-3), em cada ordem
fixa de jet, e essa melhora chega ao mesmo residual da PR #41. O sinal do
pivô não foi assumido nem demonstrado novamente. Positividade Hankel
all-order permanece aberta.

Base: `a871f18cb90fe7e5ac9726ca78eab319c68525fb` (#59).
Branch: `agent/tfvd-infinite-fourth-tail`.
A continuação é empilhada sobre `agent/native-cell-jet-tail-bounds`;
não presume que as PRs abertas tenham sido integradas à main.
As mudanças pertencem somente a `research/tfvd-infinite-fourth-tail/`.
Sem merge automático, alteração de fontes, pesos, métricas, pins ou
arquivos históricos.

## A — O que já estava demonstrado

- A PR #41 fornece a funcional de momentos, a forma bilinear e a direção
  mônica `orthogonalPolynomial`. `orthogonalPolynomial_self` identifica seu
  auto-pareamento com o pivô algébrico sem inserir sinal positivo. Usamos os
  coeficientes exatos de `CarryForcingResidual.criticalCoefficients` (#54).
  A interpretação por complemento de Schur/inversa ainda exige as hipóteses
  de não degenerescência originais; as identidades algébricas com divisão
  total não afirmam inversibilidade quando há pivôs nulos.
- A #58 fornece os jets fortes ℓ¹ dos retornos beta e kappa, os seus somatórios
  por células COMPLETAS, e a identidade Green com todos os cruzamentos.
- A #59 prova as cotas de cauda de ordem M^(-1), o transporte de erro ao
  residual crítico e `native_tail_window_acceleration`, a identidade finita
  que conserva dois bordos e um resto de quarta diferença. A versão infinita
  e a cota melhor desse resto eram precisamente a obrigação aberta.
- A identificação dos jets do readout completado com h_n já é um teorema
  da fonte. Não usamos theta, zeros, alturas, H6/K6/H7 ou uma Gram-alvo para
  construir os novos certificados. H6/K6 e as doze fontes entram somente
  na regressão posterior e são bloqueados nas dependências dos teoremas novos.

A onda permanece f_t(n)=n^(-1/2)exp(-it log n). Células têm pernas 4k+3,
4k+5 e centro 4k+4. M é cutoff material, m é ordem de jet e n é ordem
polinomial; nenhum desses índices foi identificado com profundidade vertical.
O raio complexo 1/2 abaixo é ferramenta de Cauchy, não mudança de câmera,
amplitude física ou normalização.

## B — O que foi demonstrado agora

Todos os nomes novos estão no namespace `CarryFourthTail`.
As declarações Lean são a referência precisa das hipóteses.

### 1. A quarta diferença da mesma fonte

`FourthDifference.lean` demonstra `fourth_difference_norm_le` por duas
aplicações da estimativa preexistente `baseTwoSecondDifference_norm_le`.
Os cinco pontos da quarta diferença são preservados antes de tomar normas.

A continuação complexa usa z=-1/2-iw. No disco fechado |w|≤1/2, Re z≤0
 e |z-j|≤j+1, para j=0,1,2,3. A quarta derivada espacial dá

    |Delta^4 f_w(a)| ≤ 24/a^4,                 a≥1.

`complex_fourth_bound` prova essa desigualdade. O caso z=0 é coberto sem
uma divisão pelo expoente. Cauchy é aplicado depois da diferença completa.

`RemainderJets.lean` prova `fourth_jet_bound`. `JetStencils.lean` identifica
os coeficientes explicitamente com a mesma onda material:

    f_m(a)=jet_m (t ↦ f_t(a)),
    fourthJet(m,a)=Delta^4 f_m(a),
    |Delta^4 f_m(a)| ≤ 24*2^m/a^4.

São os teoremas `fourth_jet_stencil` e
`normalized_material_fourth_bound`. O fator 1/m! está presente: os jets são
de Taylor normalizados, não derivadas cruas. Os polinômios de momentos não
foram usados para fabricar esses coeficientes materiais.

### 2. Bordo, resto e passagem legítima ao infinito

Reutilizamos literalmente a identidade da #59, com

    Bf(a)=[3f(a+2)-8f(a+1)+5f(a)]/8,
    Rf(a)=3/8 Delta^4 f(a)+1/2 Delta^4 f(a+1)+3/8 Delta^4 f(a+2).

O bordo também é uma combinação das primeiras diferenças da mesma onda.
`complex_first_bound` e `complex_boundary_bound` provam |Bf_w(a)|≤1/a
no mesmo disco. Em cada jet fixo,

    |B_m(a)| ≤ 2^m/a,       |R_m(a)| ≤ 30*2^m/a^4.

`boundary_jet_stencil` conserva exatamente os três endereços e pesos do
bordo original. `boundary_jet_vanishes` prova o desaparecimento do segundo
bordo no limite. Ele não foi apagado por convenção.

`QuarticEnvelope.lean` prova por álgebra racional e telescopagem

    sum_{k≥0} 1/[4(k+M)+3]^4 ≤ 1/[12(4M-1)^3],       M≥1.

`remainder_jets_summable` demonstra convergência absoluta do resto.
`native_jet_window` extrai os jets da identidade FINITA, conservando os dois
bordos; só depois `infinite_jet_acceleration` passa ao limite:

    sum_{k≥0} cellJet(m,k+M)
      = B_m(4M+3) + sum_{k≥0} R_m(4(k+M)+3).

Não há intercâmbio postulado de derivada com limite. O lado esquerdo já
estava identificado com a cauda do retorno global beta pela síntese ℓ¹.
A igualdade infinita vale também para M=0; as cotas racionais abaixo são
usadas somente quando M≥1.

### 3. Dois canais com erro cúbico

A observação acelerada de beta acrescenta ao prefixo apenas o bordo derivado:

    betaHat_M(t)=betaHead_M(t)+Bf_t(4M+3).

`accelerated_ordinary_jet_exact` conserva a cauda como o somatório original
de R_m. `accelerated_ordinary_jet_bound` prova

    |jet_m(beta-betaHat_M)| ≤ 30*2^m/[12(4M-1)^3].

`AcceleratedClock.lean` mantém o multiplicador material log n. Seu bordo é
B aplicado à sequência (log n)f_t(n), e a derivada física original prova

    jet_m B_clock = i(m+1) B_(m+1).

`return_clock_jet` e `finite_clock_jet` identificam a MESMA relação para os
retornos completo e finito, a partir dos jets ℓ¹ já existentes.
`accelerated_clock_jet_series` e `accelerated_clock_jet_bound` dão

    jet_m(kappa-kappaHat_M)
       = i(m+1) sum_{k≥0} R_(m+1)(4(k+M)+3),
    |jet_m(kappa-kappaHat_M)|
       ≤ 30*(m+1)*2^(m+1)/[12(4M-1)^3].

Não é um novo clock nem uma alegação sobre domínios de suas potências.
As duas quadraturas continuam complexas, com a fase original negativa.

### 4. O mesmo residual, a mesma divisão e os cruzamentos

`AcceleratedCritical.lean` mantém os multiplicadores da #59:

    A(t)=-D'(t)/(2F(t)),    B(t)=iD(t)/(2F(t)).

D, D' e F são os fatores originais completados. F não é reconstruído de
um cutoff. A observação acelerada de Q usa betaHat_M e kappaHat_M, e

    Q-QHat_M=A(beta-betaHat_M)+B(kappa-kappaHat_M).

O erro dos jets é limitado pela convolução finita dos dois novos orçamentos
com |jet_j A| e |jet_j B|. Se C_r e Ccrit(s,n) são as MESMAS constantes da
#59, `accelerated_response_budget_rate` e `accelerated_critical_error` provam

    |jet_r Q-jet_r QHat_M| ≤ 5 C_r/[4(4M-1)^3],
    |pivot(s,n)-pObsHat(s,n,M)| ≤ 5 Ccrit(s,n)/[4(4M-1)^3].

`accelerated_bilinear_error` foi provado para DOIS argumentos independentes
antes da especialização crítica. A soma mantém todos os pares i,j e usa os
coeficientes exatos da #41. Nenhum sinal de pivô é entrada.
`critical_budget_improvement` dá o ganho exato sobre a envoltória anterior:

    novo orçamento = [5/(4M-1)^2] * orçamento da #59.

Em M=16, o fator é 5/3969. Isso melhora o erro absoluto de aproximação;
não é uma desigualdade de coercividade ou uma margem positiva all-order.

`AcceleratedGreen.lean` reconstrói o mesmo par escalar do Green físico como
cabeça acelerada mais cauda. `accelerated_green_tail_ledger` retém EXATAMENTE

    E(full,full)-E(head,head)=E(head,tail)+E(tail,head)+E(tail,tail).

A forma E é `reducedCellForm` da #58, incluindo o produto assinado dos
companheiros. `accelerated_value_tail_jet_bound` e
`accelerated_companion_tail_jet_bound` conservam D e D' nas cotas dos jets
das duas componentes. Não foi escolhida outra métrica nem descartado um
termo difícil. A cabeça acelerada é uma observação corrigida do mesmo estado,
não um novo estado físico ou uma Gram substituta.
A cota crítica utiliza QHat com F completo. Não identificamos essa observação
com a normalização finita de E(head,head); o ledger HT+TH+TT é uma checagem
separada de proveniência do mesmo objeto completo, com cotas de jets para
as componentes da cauda.

### 5. Regressões racionais concretas do erro infinito

`Canary.lean` prova pelo kernel, com `norm_num` e os teoremas infinitos:

    |jet_5(beta-betaHat_501)| < 10^-8,
    |jet_5(kappa-kappaHat_1145)| < 10^-8.

Comparação dos cutoffs suficientes para ESSAS envoltórias de um único jet:

| Canal, jet 5, tolerância 10^-8 | Envoltória anterior | Acelerada |
| --- | ---: | ---: |
| Ordinário | 400000001 | 501 |
| Logarítmico | 4800000001 | 1145 |

Os valores anteriores são custos das cotas, não cutoffs ótimos da fonte.
O teste racional também compara 10^-25: a aceleração ainda exigiria cutoffs
muito grandes nesse orçamento bruto. Nenhuma campanha desse porte foi feita.
Essas tolerâncias são ABSOLUTAS dos jets materiais, não erros relativos dos
momentos h_n e não uma certificação do pivô. Não há números de zeros ou
alturas como entradas.

## C — O que foi refutado ou não decorre do resultado

Nenhuma nova obstrução contra a fonte foi demonstrada. O avanço fecha uma
lacuna de análise; não fornece uma lei de sinal.

- A etapa infinita deixou de ser uma hipótese: convergência do resto,
  desaparecimento do bordo e identificação com o retorno original foram provados.
- Positividade do resto não foi provada. Os pesos positivos na fórmula de R
  não tornam positivos os jets complexos ou a forma Green assinada.
- A aceleração não apaga a cauda. Ela a representa e limita com uma potência
  melhor, preservando todos os termos.
- Uma envoltória menor não decide sozinha de qual lado do equilíbrio o retorno
  se aproxima. Não foi provada contratividade ou positividade Hankel all-order.
- O denominador F completo continua nas observações. Ainda não temos neste PR
  intervalos certificados para seus multiplicadores A,B, nem um algoritmo que
  use somente M células e uma nova normalização finita.
- Nenhum no-go particular foi transformado em impossibilidade da geometria.
  Não foram alteradas a fonte ou a métrica para obter a melhora.

## D — Kernel, experimentos e auditoria

Os nove módulos matemáticos contêm 67 teoremas e 30 definições, totalizando
97 raízes públicas inventariadas em `public-roots.json`.
`Audit.lean` imprime axiomas e percorre transitivamente tipos E corpos,
com somente propext, Classical.choice e Quot.sound permitidos.
Todos os grupos também rejeitam `material_scale_pos`, os certificados
H6/K6/H7 e consumidores de positividade all-order. A positividade de h_0
não é usada para provar as novas cotas.

**Validação completa: 20/20 verificações com código de saída zero.**
Os nove módulos matemáticos e Audit foram compilados explicitamente com
warningAsError. Passaram os builds focado e raiz com `lake build --wfail`,
as auditorias Foundation/Geometry/Analysis, as regressões racionais e
numéricas, a regressão das doze fontes, a preservação dos arquivos
históricos e `git diff --check`.

Os fechamentos transitivos das 97 raízes públicas (tipos e corpos) tiveram
estes tamanhos por grupo: quarta diferença 2473; jets 3289; envoltória 1489;
infinito 3130; clock 3244; crítico 5639; stencils 2624; bordo 5725;
regressões racionais 5464. Só foram encontrados os três axiomas fundacionais
permitidos. Nenhuma admissão, axioma matemático ou atalho native_decide foi
introduzido.

A checagem de preservação confirmou main e origin/main em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, a #59 na base indicada acima,
as demais refs protegidas, pins, worktrees e arquivos preexistentes do
operador e da #51. Nenhuma worktree foi criada ou removida.

Reprodução no ambiente preparado da #59, host llm:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/tfvd-infinite-fourth-tail/validate.py
```

`compile_module.sh` explicita os caches das dependências de pesquisa.
Num checkout novo, preparar antes os ancestrais conforme seus relatórios.
A validação recompila explicitamente todos os módulos novos com
warningAsError e executa builds focado/raiz com `lake build --wfail`, as
três auditorias de camadas, a regressão das doze fontes e a preservação dos
arquivos/refs anteriores. Não instala pacotes ou muda pins.

`experiment.py` usa Fraction para as envoltórias racionais e mpmath 1.3.0
(Python 3.12 existente no Miniforge) para regressões FINITAS da mesma onda.
São testados a quarta diferença, o bordo logarítmico, a identidade finita
com ambos os bordos, e diferenças entre observações de cutoff M e 2048.
Não é fornecido um valor infinito externo. Esses testes não substituem as
provas Lean e não são certificados intervalares de Gamma ou de pivôs.
Logs, comandos, hashes e resultados ficam em `evidence/`.

## E — Próximo passo mínimo

A cota da quarta diferença e a passagem ao infinito não precisam mais ser
reabertas. O próximo gate concreto é a certificação dos multiplicadores do
readout COMPLETO, começando pela direção segunda par da #41, n=1:

    |jet_j A|≤alpha_j,    |jet_j B|≤beta_j,    0≤j≤5.

Esses limites devem vir dos D,D' e F originais, incluindo o controle da
inversão perto do centro por F(0)≠0, sem positividade do pivô como hipótese.
Os coeficientes beta, kappa necessários agora têm a cauda acelerada provada.
Será então possível montar intervalos da MESMA observação crítica e testar

    limite inferior de pObsHat > novo orçamento de erro.

A referência à segunda direção é uma regressão econômica; ela não transforma
seu sinal finito já conhecido numa lei universal. Se a constante ainda tornar
o cutoff inviável, a próxima melhoria deve conservar mais cancelamentos da
mesma fonte, sem ajustar momentos ou escolher outra métrica.

Para all-order continua faltando uma propriedade independente da síntese que
oriente o sinal da forma canônica completa. O controle de erro agora é mais
forte e reutilizável; essa obrigação de sinal permanece distinta.
