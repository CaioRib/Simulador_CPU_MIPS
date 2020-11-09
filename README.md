# Simulador_CPU_MIPS

### 4 de junho de 2018

Projeto para a disciplina SSC0112 que consiste em simular uma CPU, que roda intruções no formato binário segundo o modelo proposto pelo livro Patterson, D. A., Hennessy, J. L. Computer Organization and Design.

Utilizando a biblioteca pthread.h e semaphore.h, o código foi paralelizado para simular exatamente como ocorre na CPU proposta no livro, no qual porções do DataPath ocorrem de forma simultânea.

Em code.s temos uma pequena função em assembly que foi desenvolvida, decodificada para código binário e que serve de entrada para o simulador. A versão binária, em 32 bits, pode ser encontrada em code.bin, esta é uma entrada para o programa.

![alt text](https://github.com/CaioRib/Simulador_CPU_MIPS/blob/main/img/datapath.png?raw=true)

Figura 1: Datapath simulado, retirado do livro Patterson, D. A., Hennessy, J. L. Computer Organization and Design.
