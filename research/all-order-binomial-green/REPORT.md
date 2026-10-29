# Lei binomial radial em toda ordem e limite da ponte TFVD–Bessel

**Classificação: PARTIAL.** O alvo de extração binomial foi fechado no kernel
para índices arbitrários. A positividade canônica all-order continua aberta.
O inventário trouxe uma obstrução precisa à aplicação literal de um Pitágoras
já existente; não trouxe ainda a identificação física do complemento Green.

Data: 25/10/2026. Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/all-order-binomial-green`.
Base imutável: `18080d88350b5bb3a00234e1d9ae4720c0c8f3ca` (PR #88,
`agent/polarized-green-jet-four`). Esta entrega é empilhada nessa PR ainda
aberta, sem presumir sua integração à main. Nenhum merge automático.
Host de execução: `ssh llm`. Pins, fontes, amplitudes, métrica, completion e
normalizações preservados. Somente esta pasta de pesquisa foi acrescentada.

## A — O que já estava demonstrado

### Fonte e ortogonalização

A PR #88 já preservava a síntese de J0,J2,J4 e os 25 cruzamentos ordenados,
com os setores BB,BE,EB,EE. `quartic_exact_expansion` identificava termo finito,
primeira correção e termo de quarta ordem, mantendo resto analítico.
`critical_moment_pairing` e `critical_old_pairing_zero` transportavam a direção
crítica da PR #41 para o mesmo balanço físico: bastava inversibilidade do
prefixo, sem hipótese de sinal. Esses resultados não foram reimplementados.

`common_jet_pairing_tendsto`, `common_even_jets`, `common_odd_jets` e
`common_even_odd_jets`, em `radial-common-refinement/CommonJets.lean`, já davam
limites de pareamentos assinados para ordens arbitrárias, com duas escalas.
Não eram, por isso, uma realização Hilbert positiva da Hankel canônica.

### O pivô finito theta já está fechado

A lembrança do usuário está correta. No operador, no HEAD
`bfeb10fd2425400fa38139903d12bf0599f02e53`, existem:

- `nativeSourceTenthMixedNumerator_gt_rational`;
- `nativeSourceFiveEvenDiscriminant_pos`;
- `nativeSourceFiveEvenBoundaryEnergy_pos`;
- `nativeSourceFiveEvenDiscriminant_integral_formula`;
- `nativeSourceFiveEvenBoundaryEnergy_square`.

A certificação theta utiliza os integrais originais, seus modos, caudas e
intervalos. Não precisamos recertificar o pivô par n=2 para procurar sua
explicação geométrica. A entrega recompila os consumidores relevantes e
audita separadamente esse resultado finito.

A identificação de normalização também já existe:
`nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment` e
`primeDepthGeometricMoment_eq_canonical` dão b_j=2h_j. Assim a face de três
coordenadas tem discriminante 8 det(H3), prefixo 4 det(H2) e residual crítico
2 Schur(h,0,2). A forma `physicalForm` usada nesta investigação tem o fator
1/2 já definido anteriormente; seu limite lê Schur(h,0,2), como na PR #88.
Essas conversões são álgebra das definições, não novas normalizações físicas.

H6 e K6 também continuam certificados em `CarrySixthEven.even_source_six_posDef`
e `CarrySixthOdd.odd_source_six_posDef`. Portanto “oitava fonte ainda aberta”
no inventário é uma descrição histórica/local de um módulo do operador, não
uma lacuna finita global que deva substituir a investigação estrutural.
Esta rodada não reivindica uma nova prova desses certificados H6/K6.

### Inventário recebido

Foi lido como contexto matemático, sem transformar suas recomendações em
hipóteses. Arquivo:
`INVENTARIO_PITAGORICO_CARRY_TFVD_GREEN_2026-10-25.md`, 37682 bytes,
SHA256 `2a8f06d393cdd6fd7f688e2fac78ccac7b4a5b66790198961de25958547fba54`.

P09 foi conferido nas declarações originais do crosswalk do operador:
`canonicalPrimosPrimeCarryProvenance_polarized_pythagoras_of_realizesOn` e
`canonicalPrimosSeededTfvdBessel_polarized_pythagoras_of_realizesOn`.
A hipótese fixa os mesmos readouts ativos para ambos os estados.
P22 recupera a diferença assinada, P24 conserva positivo menos negativo e
P30 fornece a identidade de Schur. Nenhum deles descarrega sozinho o sinal.

## B — O que foi demonstrado agora

### B1. Coeficiente binomial em índices arbitrários

Defina os pesos originais w_p(r)=(-1)^(p-r) binom(p,r), nos nós **r+1**,
e U(p,d)=sum_r w_p(r)(r+1)^d. Foram provadas, sem momentos como entradas:

    U(p,d)=0                     se d<p,
    U(p,p)=p!,
    U(p,p+1)=p! B(p),
    U(p,p+2)=p! A(p),

com

    B(p)=(p+1)(p+2)/2,
    A(p)=(p+1)(p+2)(p+3)(3p+4)/24.

`difference_mul_coordinate` prova o comutador discreto por indução e dá a
recorrência dos deslocamentos. `mixed_coefficient_next` prova que somente
três termos sobrevivem ao produto de dois stencils independentes.

Para s=0 ou 1 (a declaração aceita qualquer s natural), escreva p=2i+s,
q=2j+s. O resultado é:

    d_s(i,j)=A(2i+s)+A(2j+s)-B(2i+s)B(2j+s).

`same_parity_first_correction` inclui o sinal de paridade explicitamente.
`original_quotient_same_parity` identifica o resultado com o quociente de
potências realmente amostrado, incluindo o denominador x+y:

    (-1)^s/(p!q!) sum_(r,t) w_p(r)w_q(t)
      [(r+1)^(p+q+3)+(t+1)^(p+q+3)]/(r+t+2) = d_s(i,j).

Não se trata de extrapolar uma tabela finita. A prova quantifica i,j,s.

### B2. Mesma fonte, extração canônica e resto preservado

`parity_source_original` conserva os jets físicos originais em qualquer
soma finita, nas duas paridades. `parity_green_vector_split` e
`parity_green_four_sectors` fazem a decomposição **vetorial** antes do readout.
`parity_source_all_crosses` mantém os produtos ordenados e a conjugação,
para dois inputs independentes e até dimensões diferentes.

`even_physical_ray` identifica exatamente o pareamento dos jets pares com
a amostragem radial original, em todo i,j. Sua hipótese é a regularidade dos
nós físicos envolvidos; os resultados existentes fornecem essa regularidade
eventualmente. A amplitude, os fatoriais, as fases e o endereço r+1 não mudam.

Em `CanonicalExtraction.lean`, `rawRay` é a combinação das amostras da
**mesma** `imaginaryReadout = -i nativeResponse(i z)`. O teorema
`raw_ray_coefficient` calcula seu coeficiente de Taylor por diferenciação
das somas finitas. `native_same_parity_first_correction` demonstra:

    [coeficiente radial normalizado de primeira correção]
      = -d_s(i,j) h_(i+j+s+1).

É uma identidade canônica sem hipótese de positividade e sem certificado
finito theta na dependência. A extração Taylor vale nas duas paridades;
a nova identidade explícita do pareamento físico a k finito foi demonstrada
no setor par. Os limites físicos das duas paridades já estavam provados.

`raw_ray_exact_remainder` conserva, para cada truncamento arbitrário,
um resto holomorfo R em uma vizinhança do centro. Não fornece uma constante
uniforme em toda ordem e não elimina R. A nova entrega não anuncia uma
estimativa uniforme dos restos de todos os jets, nem uma família infinita
de vetores Hilbert positivos.

### B3. Identidade polarizada de três pareamentos

Se M_s(c,d)=sum_(i,j)c_i d_j h_(i+j+s), defina as ações diagonais
(A_s c)_i=A(2i+s)c_i e (B_s c)_i=B(2i+s)c_i. Então, em qualquer dimensão:

    C_s(c,d) = M_(s+1)(B_s c,B_s d)
             -M_(s+1)(A_s c,d)-M_(s+1)(c,A_s d).

É `correction_bilinear_three_pairings`, com todos os cruzamentos. Nenhum
termo foi promovido a norma positiva. `correction_bilinear_canonical_pr88`
recupera exatamente a correção da PR #88, inclusive 1,20,126,14,75,55.

### B4. Localidade de Schur e separação entre sinal e correção

`source_schur_eq_of_prefix` vale em qualquer n,s: o Schur depende somente
dos momentos até 2n+s, sem necessidade de inversibilidade para essa
identidade algébrica da inversa totalizada.

Para o controle n=2, mudar apenas m5 deixa A,b,Schur e a direção crítica
inalterados, mas muda Ccrit por -55 t. `arbitrary_correction_with_fixed_schur`
permite qualquer valor da correção mantendo esses dados fixos.
Essas sequências são **controles de uma inferência genérica**, não fontes
alternativas nem perturbações permitidas da fonte canônica.

### B5. Obstrução afim da aplicação literal de P09

O arquivo novo `AffineFrameObstruction.lean` usa o predicado ORIGINAL
`IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn`.
Para uma família real-linear F:(Fin N -> complexos) -> PrimeCarryDefectGlobalHilbert,
se F(c) realiza os mesmos readouts fixos para todo c, então c=0 força:

- todos esses readouts ativos a zero;
- o estado canônico de proveniência a zero;
- a energia TFVD–Bessel semeada a zero.

São `fixed_readouts_linear_family_zero`, `_active_zero`, `_bessel_zero` e
`no_fixed_readout_linear_family_of_active_ne_zero`. As duas quadraturas reais
dos coeficientes complexos são mantidas. Isso exclui somente a identificação
literal da fibra afim existente com uma família linear homogênea de fontes.
Não exclui uma análise linear cujos readouts dependam do input.

## C — O que foi refutado e o que não foi

1. A matriz de **pesos d**, sem os momentos, já tem menor 2x2 igual a -386.
   `coefficient_two_by_two_negative` impede tratá-la como um novo kernel
   positivo por sua aparência binomial. Não é um contramodelo à Hankel nativa.
2. O controle exato m_j=1+2^j tem prefixo invertível, polinômio crítico
   x²-3x+2, Schur=0 e correção=1353>0. Portanto correção positiva não implica
   genericamente Schur estritamente positivo. Não refuta semidefinitude e
   não é um contramodelo à sequência canônica.
3. P09 com readouts fixos não fornece diretamente uma projeção linear de
   todas as fontes, conforme B5. A hipótese de realização não pode ser omitida.
4. Não se demonstrou impossibilidade geral de uma costura geométrica positiva.
   Não se demonstrou que as correções tenham sinal universal. O sinal finito
   theta não foi convertido em premissa da lei binomial.

## D — O que permanece aberto e evidência de validação

A fórmula d_s é universal para os stencils e o kernel Cauchy considerados.
Justamente por isso não distingue, sozinha, a fonte canônica de respostas
analíticas com sinais diferentes. A obrigação de sinal exige uma propriedade
**independente e específica do transporte completado**, com bordo e retorno.

P24 ainda fornece dois canais de Jordan com sinais opostos. Zerar o canal
negativo inteiro pressupõe a contração equivalente ao sinal buscado, salvo
se esse desaparecimento for derivado da geometria original. Os Pitágoras de
outros carriers não demonstram a identificação que falta.

Também não se deve substituir o retorno por uma projeção ortogonal ambiente
sem prova de transporte: `radialReturnedSynthesis_eq_incident_multiply` e
`radialReturnTransfer_mem_incidentSpan` preservam o span incidente original.
Uma identificação literal pelo mesmo embedding pode impor idempotência
extra; nenhuma realização desse tipo foi construída aqui.

**Validação concluída:** 63 teoremas novos, 19 definições (82 raízes públicas),
6617 dependências transitivas no conjunto novo, 19 comandos com exit 0.
A auditoria separada dos quatro resultados nativos reutilizados percorreu
5227 dependências, também com apenas os axiomas permitidos.

Validação reproduzível e números exatos constam de `evidence/validation.json`,
`evidence/lean-Audit.log`, `public-roots.json` e `evidence/source-provenance.json`.
Todos os módulos novos são compilados explicitamente com warningAsError;
`lake build --wfail` raiz e auditorias Foundation/Geometry/Analysis são
executados separadamente. A auditoria percorre tipos e corpos transitivos,
incluindo auxiliares privados, e separa construção, extração e sinais finitos
reutilizados. Apenas propext, Classical.choice e Quot.sound são permitidos.
O guard das identidades novas proíbe consumidores all-order condicionais e
certificados finitos de sinal. Nenhum novo axioma, sorry, admit ou native_decide.

Reprodução no servidor a partir desta branch (a .lake pode ser ligada ao
cache canônico, conforme o ambiente já utilizado):

```bash
cd research/all-order-binomial-green
python3 build_pr41.py
python3 build_upstream.py
python3 validate.py
```

As fontes recuperadas da PR #41 são imutáveis, hashadas e ignoradas em .cache.
O histórico é reutilizado sem editar a branch antiga. A compilação do root
não substitui a compilação explícita dos módulos desta pasta.

## E — Próximo passo mínimo

O alvo binomial sugerido pela PR #88 está fechado; a próxima tarefa não é
repetir o pivô theta, nem postular uma contração global.

Usar os **readouts dependentes da própria fonte** para construir a análise
linear no atlas primo que P09, com readouts fixos, não fornece diretamente.
Antes de qualquer argumento de sinal, calcular seu pareamento em dois inputs
materiais originais independentes e compará-lo ao pareamento incidente/retorno
completado, conservando o defeito e os termos de bordo.

O primeiro teste deve incluir o input zero e dois stencils básicos: F(0)=0,
calibração do termo central e um cruzamento fora da diagonal. Se os kernels
não coincidirem, explicitar a diferença; não escolher uma métrica para fazê-la
sumir. Isso testa uma construção concreta e preserva a proveniência, em vez
de introduzir um predicado equivalente à positividade como causa.

A alternativa via Jordan continua legítima somente se o comportamento do
canal negativo da **mesma fonte** for derivado de uma lei física independente.
A existência formal dos canais ou uma soma de quadrados em outro carrier
não descarrega essa obrigação.

**Fim do relatório.**
