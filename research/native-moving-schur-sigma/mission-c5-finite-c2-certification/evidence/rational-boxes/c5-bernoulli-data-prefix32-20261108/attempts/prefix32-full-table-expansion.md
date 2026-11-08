# Tentativa: prefixo 32 expandindo a tabela inteira

A prova inicial do teorema `c5BernoulliPrimeTable 32 = data.extract 0 32`
usava `norm_num [data]` com o literal completo de 601 entradas em cada um dos
32 casos da recorrência. A compilação foi interrompida após aproximadamente
5:49, antes de produzir o `.olean` do teorema; pico de RSS observado:
3,524,596 KiB. A tentativa não atingiu o limite de memória.

A prova final usa prefixos separados de 32 entradas; assim, o primeiro
certificado normaliza somente o bloco 0–32. Sua compilação limpa termina em
2:34 e usa cerca de 3.7 GiB de RSS.
