/***************************************************************
USP/ICMC/SSC - SCC0112 Organizacao de Computadores Digitais I
Trabalho 2 - Simulador de uma CPU MIPS Multiciclo 32 bits
Turma 2 - Grupo 5
Nomes:
    Vinicius Torres Dutra Maia da Costa - nUSP: 10262781
    Daniel Penna Chaves Bertazzo        - nUSP: 10349561
    Caio Abreu de Oliveira Ribeiro      - nUSP: 10262839
    Gabriel Citroni Uliana              - nUSP: 9779367

A participacao dos integrantes foi equivalente na elaboracao do trabalho, realizando reunioes
para discutir os algoritmos e utilizando ferramentas para programar em grupo (como o atom teletype).
****************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <pthread.h>
#include <semaphore.h>

//	Mascaras para obtencao dos bits(0 - 18) da variavel de controle separadamente
#define Bit0  1
#define Bit1  2
#define Bit2  4
#define Bit3  8
#define Bit4  16
#define Bit5  32
#define Bit6  64
#define Bit7  128
#define Bit8  256
#define Bit9  512
#define Bit10 1024
#define Bit11 2048
#define Bit12 4096
#define Bit13 8192
#define Bit14 16384
#define Bit15 32768
#define Bit16 65536
#define Bit17 131072
#define Bit18 262144

// Mascaras para obtencao dos bits do registrador IR que representam o codigo de operacao
#define Bit26 67108864
#define Bit27 134217728
#define Bit28 268435456
#define Bit29 536870912
#define Bit30 1073741824
#define Bit31 2147483648

//	Mascaras para obtencao dos valores dos campos do registrador IR  
#define MaskImm 65535 			//imediato para tipo-I
#define MaskTarget 33554431		//target para tipo-J
#define MaskRs 65011712			//registradores rs, rt, rd
#define MaskRt 2031616
#define MaskRd 63488
#define MaskCodFunc 63			//codigo de funcao para tipo-R

//	Mascara para obtencao dos 4 bits mais significativos de PC
#define PcConcatenate 4026531840

//	Numero de threads total do programa
#define THREADS 20

//	Semaforos para cada threads e para a main
sem_t permit[THREADS];
sem_t sem_master;

//	Variaveis goblais que representam os sinais do caminho de dados e os registradores MDR, PC e IR
int MDR, ctrl_signals, ALUOut, A, B, Address, Write_data_reg, Write_reg, AluA, AluB, PCnext, Zero, BNEout, ALUctrlOut;
int MemData, imm_extend, imm_extend_shift, ALUresult, jump_target, jump_target_shift;
short rs, rd, rt, imm, codFunc;
unsigned int PC, IR;

//	Variaveis que representam cada bit de estado, proximo estado e operacao, na unidade de controle
short S[4], NS[4], op[6];

//	Banco de registradores e memorica RAM(ordenada a byte)
int *bco_regs;
char *RAM;

/*  Função que realiza a impressão dos valores dos registradores no Banco de Registradores, das primeiras 32
palavras armazenadas em memória RAM, dos valores de PC (Program Counter), A, B,
IR (Instruction Register), MDR (Memory Data Register), da variavel de controle e de Aluout. Esta função é
chamada quando a execução das intruções é interrompida. */
void print_output(){
    printf("PC=%-20u IR=%-20u MDR=%-20u\n", PC, IR, MDR);
    printf("A=%-20d  B=%-20d  AluOut=%-20d\n", A, B, ALUOut);
    printf("Controle=%-15d\n", ctrl_signals);
    printf("\n");

    printf("Banco de Registradores\n");
    printf("R00(r0)=%-15d R08(t0)=%-15d R16(s0)=%-15d R24(t8)=%d\n", bco_regs[0], bco_regs[8], bco_regs[16], bco_regs[24]);
    printf("R01(at)=%-15d R09(t1)=%-15d R17(s1)=%-15d R25(t9)=%d\n", bco_regs[1], bco_regs[9], bco_regs[17], bco_regs[25]);
    printf("R02(v0)=%-15d R10(t2)=%-15d R18(s2)=%-15d R26(k0)=%d\n", bco_regs[2], bco_regs[10], bco_regs[18], bco_regs[26]);
    printf("R03(v1)=%-15d R11(t3)=%-15d R19(s3)=%-15d R27(k1)=%d\n", bco_regs[3], bco_regs[11], bco_regs[19], bco_regs[27]);
    printf("R04(a0)=%-15d R12(t4)=%-15d R20(s4)=%-15d R28(gp)=%d\n", bco_regs[4], bco_regs[12], bco_regs[20], bco_regs[28]);
    printf("R05(a1)=%-15d R13(t5)=%-15d R21(s5)=%-15d R29(sp)=%d\n", bco_regs[5], bco_regs[13], bco_regs[21], bco_regs[29]);
    printf("R06(a2)=%-15d R14(t6)=%-15d R22(s6)=%-15d R30(fp)=%d\n", bco_regs[6], bco_regs[14], bco_regs[22], bco_regs[30]);
    printf("R07(a3)=%-15d R15(t7)=%-15d R23(s7)=%-15d R31(ra)=%d\n", bco_regs[7], bco_regs[15], bco_regs[23], bco_regs[31]);
    printf("\n");

    printf("Memoria (enderecos a byte)\n");
    for(int i = 0; i <= 28; i += 4)
        printf("[%.2d]=%-18d [%.2d]=%-18d [%.2d]=%-18d [%.2d]=%-18d\n", i, *(int*)&RAM[i], (i+32), *(int*)&RAM[(i+32)], (i+64), *(int*)&RAM[(i+64)], (i+96), *(int*)&RAM[(i+96)]);

    free(RAM);
    free(bco_regs);
}

/*  Função que simula a Unidade de Controle, determinando, por meio de equações
logicas com o estado atual e o codigo de operacao, os sinais de controle e o próximo estado. 
A execucao desta funcao so ocorre quando, no loop da funcao main que representa o clock, 
ocorre o sem_post() para o semaforo que bloqueia a execucaco desta funcao. O semaforo correspondente
a esta funcao eh o de posicao 0 no vetor de semaforos (permit). */
void* control(){
    while(1){
        //  Execucao bloqueada ate que um sem_post() seja feito na funcao main.
        sem_wait(&permit[0]);
        
        ctrl_signals = 0;
        short RegDst[2], RegWrite, ALUSrcA, ALUSrcB[2], ALUOp[2], PCSource[2], PCWriteCond, PCWrite;
        short IorD, MemRead, MemWrite, BNE, IRWrite, MemtoReg[2];

        /*  Equacoes logicas para os sinais de controle*/

        RegDst[0] = !S[3] & S[2] & S[1] & S[0]; 	// O bit menos significativo do Sinal RegDst ativado apenas no estado 7.
        RegDst[1] = S[3] & !S[2] & S[1] & S[0]; 	// O bit mais significativo do Sinal RegDst ativado apenas no estado 11.
        
        //  Sinal RegWrite ativado  nos estados 4, 7, 10, 11 e 15
        RegWrite =  (!S[3] & S[2] & !S[1] & !S[0]) | (!S[3] & S[2] & S[1] & S[0]) | (S[3] & !S[2] & S[1] & !S[0]) | (S[3] & !S[2] & S[1] & S[0]) | (S[3] & S[2] & S[1] & S[0]);

        //  Sinal ALUSrcA ativado  nos estados 2, 6, 8, 12 e 13.
        ALUSrcA = (!S[3] & !S[2] & S[1] & !S[0]) | (!S[3] & S[2] & S[1] & !S[0]) | (S[3] & !S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & S[0]);

        // O bit menos significativo do sinal ALUSrcB eh ativado nos estados 0 e 1.
        ALUSrcB[0] = (!S[3] & !S[2] & !S[1] & !S[0]) | (!S[3] & !S[2] & !S[1] & S[0]);

        // O bit mais significativo do sinal ALUSrcB eh ativado nos estados 1, 2 e 12.
        ALUSrcB[1] = (!S[3] & !S[2] & !S[1] & S[0]) | (!S[3] & !S[2] & S[1] & !S[0]) | (S[3] & S[2] & !S[1] & !S[0]);

        // O bit menos significativo do sinal ALUOp eh ativado nos estados 0 e 1.
        ALUOp[0] = (S[3] & !S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & S[0]);

        // O bit mais significativo do sinal ALUOp eh ativado nos estados 6 e 12.
        ALUOp[1] = (!S[3] & S[2] & S[1] & !S[0]) | (S[3] & S[2] & !S[1] & !S[0]);

        // O bit menos significativo do sinal PCSource eh ativado nos estados 8, 13, 14 e 15.
        PCSource[0] = (S[3] & !S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & S[0]) | (S[3] & S[2] & S[1] & !S[0]) | (S[3] & S[2] & S[1] & S[0]);

        // O bit mais significativo do sinal PCSource eh ativado nos estados 9, 11, 14 e 15.
        PCSource[1] = (S[3] & !S[2] & !S[1] & S[0]) | (S[3] & !S[2] & S[1] & S[0]) | (S[3] & S[2] & S[1] & !S[0]) | (S[3] & S[2] & S[1] & S[0]);

        //  Sinal PCWriteCond ativado nos estados 8, 12 e 13.
        PCWriteCond = (S[3] & !S[2] & !S[1] & !S[0]) | (S[3] & S[2] & !S[1] & S[0]);

        //  Sinal PCWrite ativado nos estados 0, 9, 11, 14 e 15.
        PCWrite = (!S[3] & !S[2] & !S[1] & !S[0]) | (S[3] & !S[2] & !S[1] & S[0]) | (S[3] & !S[2] & S[1] & S[0]) | (S[3] & S[2] & S[1] & !S[0]) | (S[3] & S[2] & S[1] & S[0]);

        //  Sinal IorD ativado nos estados 3 e 5.
        IorD = (!S[3] & !S[2] & S[1] & S[0]) | (!S[3] & S[2] & !S[1] & S[0]);

        //  Sinal MemRead ativado nos estados 0 e 3.
        MemRead = (!S[3] & !S[2] & !S[1] & !S[0]) | (!S[3] & !S[2] & S[1] & S[0]);

        //  Sinal MemWrite ativado nos estado 5.
        MemWrite = (!S[3] & S[2] & !S[1] & S[0]);

        //  Sinal BNE ativado no estado 13.
        BNE = (S[3] & S[2] & !S[1] & S[0]);

        //  Sinal IRWrite ativado no estado 0.
        IRWrite = (!S[3] & !S[2] & !S[1] & !S[0]);

        // O bit menos significativo do sinal MemtoReg eh ativado no estado 4.
        MemtoReg[0] = (!S[3] & S[2] & !S[1] & !S[0]);

        // O bit mais significativo do sinal MemtoReg eh ativado no estado 13 e 15.
        MemtoReg[1] = (S[3] & !S[2] & S[1] & S[0]) | (S[3] & S[2] & S[1] & S[0]);

        /*  Juncao de todos os sinais de controle em um unico inteiro (ctrl_signals)
        de 32 bits, sendo atribuido a cada um dos 18 bits menos significativos um
        sinal de controle, por meio das mascaras. */
        ctrl_signals = Bit18*MemtoReg[1] + Bit17*MemtoReg[0] + Bit16*IRWrite + Bit15*BNE + Bit14*MemWrite +
                       Bit13*MemRead + Bit12*IorD + Bit11*PCWrite + Bit10*PCWriteCond + Bit9*PCSource[1] +
                       Bit8*PCSource[0] + Bit7*ALUOp[1] + Bit6*ALUOp[0] + Bit5*ALUSrcB[1] + Bit4*ALUSrcB[0] +
                       Bit3*ALUSrcA + Bit2*RegWrite + Bit1*RegDst[1] + Bit0*RegDst[0];

        /* Funcao Proximo Estado Explicita */
        // Bit menos significativo do proximo estado eh ativado nas situacoes:
        NS[0] = (!S[3] & !S[2] & !S[1] & !S[0]) |                                                      // Estado 0
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & op[2] & !op[1] & op[0]) |   // Estado 1 e op = bne
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |   // Estado 1 e op = jal
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & op[1] & !op[0]) |  // Estado 1 e op = j
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & op[0]) |    // Estado 1 e op = jalr
                (!S[3] & S[2] & S[1] & !S[0]) |                                                        // Estado 6
                (!S[3] & !S[2] & S[1] & !S[0] & op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |    // Estado 2 e op = lw
                (!S[3] & !S[2] & S[1] & !S[0] & op[5] & !op[4] & op[3] & !op[2] & op[1] & op[0]);      // Estado 2 e op = sw

        // Segundo bit menos significativo do proximo estado eh ativado nas situacoes:
        NS[1] = (!S[3] & !S[2] & !S[1] & S[0] & op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |    // Estado 1 e op = lw
                (!S[3] & !S[2] & !S[1] & S[0] & op[5] & !op[4] & op[3] & !op[2] & op[1] & op[0]) |     // Estado 1 e op = sw
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & op[3] & !op[2] & !op[1] & !op[0]) |  // Estado 1 e op = addi
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & !op[1] & !op[0]) | // Estado 1 e op = tipo-R
                (!S[3] & !S[2] & S[1] & !S[0] & op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |    // Estado 2 e op = lw
                (!S[3] & S[2] & S[1] & !S[0]) |                                                        // Estado 6
                (!S[3] & !S[2] & S[1] & !S[0] & !op[5] & !op[4] & op[3] & !op[2] & !op[1] & !op[0]) |  // Estado 2 e op = addi
                (S[3] & S[2] & !S[1] & !S[0]) |                                                        // Estado 12
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |   // Estado 1 e op = jal
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & !op[0]) |   // Estado 1 e op = jr
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & op[0]);     // Estado 1 e op = jalr


        // Terceiro bit menos significativo do proximo estado eh ativado nas situacoes:
        NS[2] = (!S[3] & !S[2] & S[1] & S[0]) | (!S[3] & S[2] & S[1] & !S[0]) |                        // Estado 3 ou 6
                (!S[3] & !S[2] & S[1] & !S[0] & op[5] & !op[4] & op[3] & !op[2] & op[1] & op[0]) |     // Estado 2 e op = sw
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & !op[1] & !op[0]) | // Estado 1 e op = tipo-r
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & op[3] & op[2] & !op[1] & !op[0]) |   // Estado 1 e op = andi
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & op[2] & !op[1] & op[0]) |   // Estado 1 e op = bne
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & !op[0]) |   // Estado 1 e op = jr
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & op[0]);     // Estado 1 e op = jalr

        // Bit mais significativo do proximo estado eh ativado nas situacoes:
        NS[3] = (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & op[3] & op[2] & !op[1] & !op[0]) |   // Estado 1 e op = andi
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & op[2] & !op[1] & op[0]) |   // Estado 1 e op = bne
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & !op[0]) |   // Estado 1 e op = jr
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & op[4] & !op[3] & op[2] & !op[1] & op[0])  |   // Estado 1 e op = jalr
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & op[2] & !op[1] & !op[0]) |  // Estado 1 e op = beq
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & op[1] & op[0]) |   // Estado 1 e op = jal
                (!S[3] & !S[2] & !S[1] & S[0] & !op[5] & !op[4] & !op[3] & !op[2] & op[1] & !op[0]) |  // Estado 1 e op = j
                (!S[3] & !S[2] & S[1] & !S[0] & !op[5] & !op[4] & op[3] & !op[2] & !op[1] & !op[0]) |  // Estado 2 e op = addi
                (S[3] & S[2] & !S[1] & !S[0]);                                                         // Estado 12


        /* Caso de instrucao invalida (quando se esta no estado 1 e o proximo
        estado eh o 0, pois nao encontrou-se instrucao valida). Encerra-se a execucao imprimindo na tela os dados de saida */
        if((!S[3] & !S[2] & !S[1] & S[0]) && (!NS[3] & !NS[2] & !NS[1] & !NS[0])){
            printf("Stauts da Saida: Termino devido a tentativa de execucao de instrucao invalida\n\n");
            print_output();
            exit(0);
        }

        //  Avanco para o proximo estado.
        S[0] = NS[0]; S[1] = NS[1]; S[2] = NS[2]; S[3] = NS[3];

        //  Liberacao da execucao das threads: memory_read, alu_control, PC_write e IR_write
        for(int i = 2; i <= 5; i++)
            sem_post(&permit[i]);

        /*  Liberacao da execucao das threads: registers_write, mux_IorD, mux_RegDst,
        mux_MemToReg, mux_ALUsrcA, mux_ALUSrcB, mux_PCsource e mux_BNE*/
        for(int i = 8; i <= 15; i++)
            sem_post(&permit[i]);

        //  Liberacao da execucao da thread memory_write
        sem_post(&permit[19]);

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/*  Funcao que simula o funcionamento da Unidade Logica e Aritmetica, que, a partir
do sinal de controle da Unidade de Controle auxiliar para a ALU (ALUcontrol), realiza as opercoes
de soma, subtracao, ou (bitwise or), ou negado (bitwise nor)  e comparacao de "menor
que" com os operandos A e B. Alem disso, possui uma variavel que indica se o resultado
da operacao realizada eh zero. Caso receba da ALUcontrol um sinal invalido, termina
a execucao do programa, com status de saida e chamada da funcao print_output().
O semaforo correspondente a esta funcao eh o de posicao 1 no vetor de semaforos
(permit). */
void* ALU(){
    while(1){
        /* Execucao bloqueada ate que ocorram 3 sem_posts() no semaforo correspondente
        a esta thread, um na thread mux_ALUsrcA, um na thread mux_ALUSrcB e um
        da ALUcontrol, para que as entradas e o sinal de controle estejam corretos. */
        for(int i = 0; i < 3; i++) sem_wait(&permit[1]);

        //  'E' (bitwise and) quando ALUctrlOut = 0
        if(ALUctrlOut == 0){
            ALUresult = AluA & AluB;
        }

        // 'OU' (bitwise or) quando ALUctrlOut = 1
        else if(ALUctrlOut == 1)
            ALUresult = AluA | AluB;

        // Soma quando ALUctrlOut = 2
        else if(ALUctrlOut == 2)
            ALUresult = AluA + AluB;

        //  Subtracao quando ALUctrlOut = 6
        else if(ALUctrlOut == 6)
            ALUresult = AluA - AluB;

        //  Operacao de 'menor que' quando ALUctrlOut = 7
        else if(ALUctrlOut == 7){
            if(AluA < AluB)
                ALUresult = 1;
            else
                ALUresult = 0;
        }

        // Operacao de 'ou negado' (bitwise nor) quando ALUctrlOut = 12
        else if(ALUctrlOut == 12)
            ALUresult = ~(AluA | AluB);

        /*  Caso em que o sinal de controle de operacao nao eh valido, a Execucao
        do programa eh encerrada com o status da saida e chamada da funcao print_output(). */
        else{
            printf("Status de Saida: Termino devido a operacao invalida na ULA\n\n");
            print_output();
            exit(0);
        }

        /*  Caso o resultado da operacao executada pela ALU seja 0, a variavel
        Zero recebe o valor 1. Caso nao, Zero recebe o valor 0. */
        if(ALUresult == 0)
            Zero = 1;
        else
            Zero = 0;

        //  Liberacao da execucao das threads mux_PCsource e mux_BNE, respectivamente.
        sem_post(&permit[14]);
        sem_post(&permit[15]);

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/*  Funcao que simula os acessos a memoria para leitura. Em caso de acesso a posicao
nao existente no vetor que simula a memoria RAM, finaliza a execucao do programa com
mensagem de status da saida seguida da chamada da funcao print_output(). O semaforo correspondente
a esta funcao eh o de posicao 2 no vetor de semaforos (permit).*/
void* memory_read(){
    while(1){
        // So pode ser executado apos a execucao das threads que simulam a Unidade de controle e o mux_IorD.
        for(int i = 0; i < 2; i++) sem_wait(&permit[2]);

        //Caso de acesso a posicao inexistente no vetor que reprenta a memoria RAM.
        if(Address < 0 || Address > 255){
            printf("Stauts da Saida: Termido devido a acesso invalido de memoria\n\n");
            print_output();
            exit(0);
        }

        //Variavel auxiliar de um ponteiro para ler uma palavra de memoria
        unsigned int* Word;
        Word = (unsigned int*) &RAM[Address];	

        //Leitura da posicao indicada e armazena no sinal MemData.
        if(ctrl_signals & Bit13){
            MemData = *Word;
        }

        //  Liberacao da execucao das threads IR_write e MDR_write, respectivamente.
        sem_post(&permit[5]);
        sem_post(&permit[16]);

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/*  Funcao que simula os acessos a memoria para escrita. Em caso de acesso a posicao
nao existente no vetor que simula a memoria RAM, finaliza a execucao do programa com
mensagem de erro seguida da chamada da funcao print_output(). O semaforo correspondente
a esta funcao eh o de posicao 19 no vetor de semaforos (permit).*/
void* memory_write(){
    while(1){

        /* Execucao bloqueada ate que ocorram 3 sem_posts() no semaforo correspondente
        a esta thread, um na thread registers_read, um na thread mux_IorD e um
        na Unidade de controle, para que as entradas e os sinais de controle
        estejam corretos. */
        for(int i = 0; i < 3; i++) sem_wait(&permit[19]);

        //Caso de acesso a posicao inexistente no vetor que reprenta a memoria RAM.
        if(Address < 0 || Address > 255){
            printf("Stauts da Saida: Termino devido a acesso invalido de memoria\n\n");
            print_output();
            exit(0);
        }

        //Variavel auxiliar de um ponteiro para escrever uma palavra de memoria
        int* Word;
        Word = (int*) &RAM[Address];

        // Escrita no vetor que representa a RAM, na posicao correspondente, o conteudo do sinal B, como indicado no caminho de dados.
        if(ctrl_signals & Bit14){
            *Word = B;
        }

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/*  Unidade de controle auxiliar, que define a operacao que sera executada na ALU.
Em caso de uma operacao do tipo-r que tenha o campo de funcao que nao define uma
operacao na ALU, encerra-se a execucao do programa, com uma mensagem de erro.
O semaforo correspondente a esta funcao eh o de posicao 3 no vetor de semaforos
(permit).*/
void* ALUcontrol(){
    while(1){

        /* Execucao bloqueada ate que ocorram 2 sem_posts() no semaforo correspondente
        a esta thread, um na thread IR_read e um na Unidade de Controle, para que
        as entradas e os sinais de controle estejam corretos. */
        for(int i = 0; i < 2; i++)  sem_wait(&permit[3]);


        if(ctrl_signals & Bit7){
            // Caso ALUOp == 11, o sinal de controle ALUctrlOut recebe o valor 0 ('e' (bitwise and))
            if(ctrl_signals & Bit6)
                ALUctrlOut = 0;

            /* Caso ALUOp == 10, a operacao que esta sendo executada eh do tipo-r,
            entao a operacao da ALU depende do campo de funcao. */
            else{
                //  Caso codigo de funco seja 32 (Add), ALUctrlOut recebe o valor 2
                if(codFunc == 32)
                    ALUctrlOut = 2;

                //  Caso codigo de funco seja 34 (Sub), ALUctrlOut recebe o valor 6
                else if(codFunc == 34)
                    ALUctrlOut = 6;

                //  Caso codigo de funco seja 36 (And), ALUctrlOut recebe o valor 0
                else if(codFunc == 36)
                    ALUctrlOut = 0;

                //  Caso codigo de funco seja 37 (Or), ALUctrlOut recebe o valor 1
                else if(codFunc == 37)
                    ALUctrlOut = 1;

                //  Caso codigo de funco seja 42 (Slt), ALUctrlOut recebe o valor 7
                else if(codFunc == 42)
                    ALUctrlOut = 7;

                /*  Caso nao corresponda a nenhum dos campos de funcao especificados,
                a funcao eh invalida. */
                else{
                    printf("Stauts da Saida: Termino devido a tentativa de execucao de instrucao invalida\n\n");
                    print_output();
                    exit(0);

                }
            }
        }

        else{
            // Caso ALUOp == 01, o sinal de controle ALUctrlOut recebe o valor 6 (subtracao)
            if(ctrl_signals & Bit6)
                ALUctrlOut = 6;   //sub direto

            // Caso ALUOp == 00, o sinal de controle ALUctrlOut recebe o valor 2 (adicao)
            else
                ALUctrlOut = 2;   //add direto
        }

        //  Liberacao da execucao da thread ALU
        sem_post(&permit[1]);

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/*  Funcao que simula o funcionamento do bloco logico em que ocorre a escrita em
PC (Program Counter), a partir dos sinais da unidade de controle. O semaforo
correspondente a esta funcao eh o de posicao 4 no vetor de semaforos (permit).*/
void* PC_write(){
    while(1){

        /* Execucao bloqueada ate que ocorram 3 sem_posts() no semaforo correspondente
        a esta thread, um da thread mux_PCsource, um da Unidade de Controle e um da mux_BNE
        para que as entradas e os sinais de controle estejam corretos. */
        for(int i = 0; i < 3; i++) sem_wait(&permit[4]);

        /*  Escrita em PC caso o Sinal a variavel BNEout tenha valor diferente de
        0 e o sinal PCWriteConde esteja ativado ou quanddo o sinal PCWrite esteja
        ativado. */
        if((BNEout && (ctrl_signals & Bit10)) || (ctrl_signals & Bit11))
            PC = PCnext;

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que escreve a instrucao da memoria no IR (Instruction Register). O
semaforo correspondente a esta funcao eh o de posicao 5 no vetor de semaforos
(permit). */
void* IR_write(){
    while(1){

        /* Execucao bloqueada ate que ocorram 2 sem_posts() no semaforo correspondente
        a esta thread, um da thread Mem_Read e outro da Unidade de Controle, para que
        as entradas e os sinais de controle estejam corretos. */
        for(int i = 0; i < 2; i++) sem_wait(&permit[5]);

        // Se o sinal "IRWrite" (representado pelo bit 16) estiver ativado, escreve a instrucao lida da memoria (MemData) no IR
        if(ctrl_signals & Bit16){
            IR = MemData;
        }


        // Realiza um sem_post() no semaforo que bloqueia o IR_read
        sem_post(&permit[6]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que le e interpreta a instrucao previamente carregada e armazenada em IR.
O semaforo correspondente a esta funcao eh o de posicao 6 no vetor de semaforos (permit). */
void* IR_read(){
    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread, o qual esta na thread IR_write */
        sem_wait(&permit[6]);

        /* Obtem o codigo da operacao, utilizando as mascaras e um shift que retorna o bit para a posicao menos significativa*/
        op[5] = (short)((IR & Bit31) >> 31);
        op[4] = (short)((IR & Bit30) >> 30);
        op[3] = (short)((IR & Bit29) >> 29);
        op[2] = (short)((IR & Bit28) >> 28);
        op[1] = (short)((IR & Bit27) >> 27);
        op[0] = (short)((IR & Bit26) >> 26);

        /*	Obtem os registradores rs, rt, rd , por meio das mascaras e de um shift para retornar os bits 
        para as posicoes menos significativas*/
        rs = (short)((IR & MaskRs) >> 21);
        rt = (short)((IR & MaskRt) >> 16);
        rd = (short)((IR & MaskRd) >> 11);

        /* Obtem o valor do Immediate, por meio da utilizacao de sua mascara*/
        imm = (short)((IR & MaskImm));
        /* Obtem o valor do jump, por meio da utilizacao de sua mascara*/
        jump_target = (IR & MaskTarget);
        /* Obtem o valor do codigo da funcao, por meio da utilizacao de sua mascara*/
        codFunc = (short)((IR & MaskCodFunc));

        // Realiza um sem_post() no semaforo que bloqueia o shift_left_target
        sem_post(&permit[18]);
        // Realiza um sem_post() no semaforo que bloqueia o registers_read
        sem_post(&permit[7]);
        // Realiza um sem_post() no semaforo que bloqueia o mux_RegDst
        sem_post(&permit[10]);
        // Realiza um sem_post() no semaforo que bloqueia o sign_extend_and_shift_left_imm
        sem_post(&permit[17]);
        // Realiza um sem_post() no semaforo que bloqueia o ALUcontrol
        sem_post(&permit[3]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que le o numero correspondentes aos registradores "rs" e "rt" no banco de registradores
e armazena o conteudo de tais registradores no "A" e "B" para serem usados pela ULA, caso alguma
operacao seja realizada com eles. O semaforo correspondente a esta funcao eh o de posicao 7
no vetor de semaforos (permit). */
void* registers_read(){
    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread, o qual esta na thread IR_read, para que a entrada e o sinal de
        controle e sinal de controle estejam corretos*/
        sem_wait(&permit[7]);
        // Guarda os indices dos registradores "rs" e "rt" para que sejam buscados no banco de registradores
        short read_reg1 = rs;
        short read_reg2 = rt;

        // Busca o conteudo dos registradores correspondentes no banco de registradores e armazena nos sinais A e B
        A = bco_regs[read_reg1];
        B = bco_regs[read_reg2];

        /* Realiza 3 sem_posts(): um no semaforo que bloqueia o mux_ALUsrcA, outro que bloqueia o mux_ALUSrcB
        e um que bloqueia o mux_PCsource. */
        for(int i = 12; i <= 14; i++) sem_post(&permit[i]);
        // Realiza um sem_post() no semaforo que bloqueia o memory_write
        sem_post(&permit[19]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que escreve o conteudo desejado no registrador de destino. O semaforo correspondente a
esta funcao eh o de posicao 8 no vetor de semaforos (permit). */
void* registers_write(){
    while(1){

        /* Execucao bloqueada ate que ocorram 3 sem_posts() no semaforo correspondente
        a esta thread, um da thread mux_RegDst, um da mux_MemToReg e um da Unidade de controle, 
        para que as entradas e os sinais de controle estejam corretos. */
        for(int i = 0; i < 3; i++) sem_wait(&permit[8]);

        // Se o sinal "RegWrite" (representado pelo bit 2) estiver ativado, escreve o conteudo no registrador de destino
        if(ctrl_signals & Bit2)
            bco_regs[Write_reg] = Write_data_reg;

        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina se o endereco a ser acessado na memoria sera o conteudo de PC
ou do ALUOut. O semaforo correspondente a esta funcao eh o de posicao 9
no vetor de semaforos (permit). */
void* mux_IorD(){
    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread, o qual esta na thread Unidade de controle, para que a
        entrada e o sinal de controle estejam corretos*/
        sem_wait(&permit[9]);

        // Se o sinal "IorD" (representado pelo bit 12) estiver ativado, o endereco recebe o conteudo ALUOut
        if(ctrl_signals & Bit12){
            Address = ALUOut;
        }
        // Caso contrario, o endereco recebe o conteudo de PC
        else
            Address = PC;

        // Realiza um sem_post() no semaforo que bloqueia o memory_read
        sem_post(&permit[2]);
        // Realiza um sem_post() no semaforo que bloqueia o memory_write
        sem_post(&permit[19]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina qual registrador sera o registrador de destino da instrucao. O semaforo
correspondente a esta funcao eh o de posicao 10 no vetor de semaforos (permit). */
void* mux_RegDst(){
    while(1){
        /* Execucao bloqueada ate que ocorra 2 sem_posts() no semaforo correspondente
        a esta thread, da thread IR_read e outro da Unidade de Controle,
        para que a entrada e o sinal de controle estejam corretos*/
        for(int i = 0; i < 2; i++) sem_wait(&permit[10]);


        // Se o sinal "RegDst1" (representado pelo bit 1) estiver ativado, o sinal que representa o registrador de destino
        // (Write_reg) recebe o valor 31
        if(ctrl_signals & Bit1)
            Write_reg = 31;
        // Se o sinal "RegDst0" (representado pelo bit 0) estiver ativado, o Write_reg recebe o indice de "rd" (IR[15..11])
        else if(ctrl_signals & Bit0)
            Write_reg = rd;
        /* Se o sinal "RegDst0" (representado pelo bit 0) e "RegDst1" (representado pelo bit 1)
        estiverem desativados, o Write_reg recebe o indice de "rt", IR[20..16] */
        else
            Write_reg = rt;

        // Realiza um sem_post() no semaforo que bloqueia o registers_write
        sem_post(&permit[8]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina o que o registrador de destino recebera como conteudo. O semaforo correspondente
a esta funcao eh o de posicao 11 no vetor de semaforos (permit). */
void* mux_MemToReg(){

    while(1){
        /* Execucao bloqueada ate que ocorra 2 sem_post() no semaforo correspondente
        a esta thread, um da thread MDR_write e outro da Unidade de Controle,
        para que a entrada e o sinal de controle estejam corretos*/
        for(int i = 0; i < 2; i++) sem_wait(&permit[11]);

        /* Se o sinal "MemtoReg1" (representado pelo bit 18) estiver ativado,
        o sinal que representa o conteudo a ser escrito (Write_data_reg) no resgistrador de destino recebe o valor contido em PC*/
        if(ctrl_signals & Bit18)
            Write_data_reg = PC;
        /* Se o sinal "MemtoReg0" (representado pelo bit 17) estiver ativado,
        o Write_data_reg recebe o valor contido em MDR*/
        else if(ctrl_signals & Bit17)
            Write_data_reg = MDR;
        /* Se os sinais "MemtoReg1" (representado pelo bit 18)  e "MemtoReg0"
        (representado pelo bit 17) estiverem desativados, o Write_data_reg recebe
        o valor contido em ALUOut */
        else
            Write_data_reg = ALUOut;

        // Realiza um sem_post() no semaforo que bloqueia o registers_write
        sem_post(&permit[8]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina o conteudo do primeiro operando da ULA ("PC" ou conteudo de "A"). O semaforo
correspondente a esta funcao eh o de posicao 12 no vetor de semaforos (permit). */
void* mux_ALUsrcA(){
    while(1){
        /* Execucao bloqueada ate que ocorra 2 sem_post() no semaforo correspondente
        a esta thread, um da thread registers_read e outro da Unidade de Controle,
        para que a entrada e o sinal de controle estejam corretos*/
        for(int i = 0; i < 2; i++) sem_wait(&permit[12]);

        // Se o sinal "ALUSrcA" (representado pelo bit 3) estiver ativado, o AluA recebe o conteudo do sinal A
        if(ctrl_signals & Bit3)
            AluA = A;
        // Se o sinal "ALUSrcA" estiver desativado, o AluA recebe o conteudo de PC
        else
            AluA = PC;

        // Realiza um sem_post() no semaforo que bloqueia o ALU
        sem_post(&permit[1]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina o conteudo do segundo operando da ULA (conteudo de "B", 4,
IR[15..0] com extensao de sinal ou IR[15..0] com extensao de sinal e com 2 shifts left).
O semaforo correspondente a esta funcao eh o de posicao 13 no vetor de semaforos (permit).*/
void* mux_ALUsrcB(){
        while(1){
        /* Execucao bloqueada ate que ocorra 3 sem_post() no semaforo correspondente
        a esta thread, um da thread registers_read, um da Unidade de Controle e outro
        da thread sign_extend_and_shift_left_imm, para que a entrada e o sinal de
        controle e sinal de controle estejam corretos*/
        for(int i = 0; i < 3; i++) sem_wait(&permit[13]);

        // Se o sinal "ALUSrcB1" (representado pelo bit 5) estiver ativado
        if(ctrl_signals & Bit5){

            /* Se o sinal "ALUSrcB0" (representado pelo bit 4) estiver ativado,
            o AluB recebe do valor de imm_extend_shift, valor do campo imediato de IR com extensao de sinal e shift para esquerda */
            if(ctrl_signals & Bit4)
                AluB = imm_extend_shift;	//signal extend e shift left
            /* Se o sinal "ALUSrcB0" estiver desativado, o AluB recebe o valor do campo imediato de IR com extensao de sinal */
            else{
                AluB = imm_extend;       //signal extend
            }
        }

        // Se o sinal "ALUSrcB1" estiver desativado
        else{
            /* Se o sinal "ALUSrcB0" (representado pelo bit 4) estiver ativado,
            o AluB recebe o valor 4 */
            if(ctrl_signals & Bit4)
                AluB = 4;
            /* Se o sinal "ALUSrcB0" estiver desativado, o AluB recebe o valor do sinal B */
            else
                AluB = B;
        }

        // Realiza um sem_post() no semaforo que bloqueia o ALU
        sem_post(&permit[1]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que determina o endereco da proxima instrucao a ser realizada, ou seja,
o valor do PC do proximo ciclo. O semaforo correspondente a esta funcao eh o de posicao
14 no vetor de semaforos (permit). */
void* mux_PCsource(){
    while(1){
        /* Execucao bloqueada ate que ocorra 4 sem_post() no semaforo correspondente
        a esta thread, um da thread ALU, um da shift_left_target,
        um da registers_read e outro da Unidade de Controle, para que a entrada
        e o sinal de controle estejam corretos*/
        for(int i = 0; i < 4; i++) sem_wait(&permit[14]);

        // Se o sinal "PCSource1" (representado pelo bit 9) estiver ativado
        if(ctrl_signals & Bit9){

            /* Se o sinal "PCSource0" (representado pelo bit 8) estiver ativado,
            o sinal PCnext recebe do valor contido no sinal A */
            if(ctrl_signals & Bit8){
                PCnext = A;
            }
            /* Se o sinal "PCSource0" estiver desativado,
            o sinal PCnext recebe do valor contido no sinal jump_target_shift, que representa o target para um jump, apos o shift*/
            else
                PCnext = jump_target_shift;
        }
        // Se o sinal "PCSource1" estiver desativado
        else{
            /* Se o sinal "PCSource0" (representado pelo bit 8) estiver ativado,
            o PCnext recebe do valor contido em ALUOut */
            if(ctrl_signals & Bit8)
                PCnext = ALUOut;
            /* Se o sinal "PCSource0" estiver desativado,
            o PCnext recebe do valor contido em ALUresult */
            else
                PCnext = ALUresult;
        }

        // Realiza um sem_post() no semaforo que bloqueia o PC_write
        sem_post(&permit[4]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que checa se o desvio do BEQ ou BNE deve ou nao ser executado. O semaforo correspondente
a esta funcao eh o de posicao 15 no vetor de semaforos (permit). */
void* mux_BNE(){
    while(1){
        /* Execucao bloqueada ate que ocorra 2 sem_post() no semaforo correspondente
        a esta thread, um da thread ULA e outro da Unidade de Controle,
        para que a entrada e o sinal de controle estejam corretos*/
        for(int i = 0; i < 2; i++) sem_wait(&permit[15]);

        // Se o sinal "BNE" (representado pelo bit 15) estiver ativado, o BNEout recebe o valor do sinal zero da alu negado,
        // pois a operacao sera BNE
        if(ctrl_signals & Bit15)
            BNEout = !Zero;
        // Se o sinal "BNE" estiver desativado, o BNEout recebe o valor do sinal Zero da ALU, pois a operacao sera BEQ
        else
            BNEout = Zero;

        // Realiza um sem_post() no semaforo que bloqueia o PC_write
        sem_post(&permit[4]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que escreve o conteudo lido da memoria no MDR. O semaforo correspondente
a esta funcao eh o de posicao 16 no vetor de semaforos (permit). */
void* MDR_write() {

    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread da thread memory_read, para que a entrada e o
        sinal de controle e sinal de controle estejam corretos*/
        sem_wait(&permit[16]);

        // MDR (MemoryDataRegister) recebe o valor contido no sinal MemData, que representa o conteudo lido da memoria
        MDR = MemData;

        // Realiza um sem_post() no semaforo que bloqueia o mux_MemToReg
        sem_post(&permit[11]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que armazena os valores do campo de imediato (IR[15..0]) com extensao de sinal e com extensao
de sinal e shift para esquerda de duas posicoes. O semaforo correspondente a esta funcao eh o de posicao 17 no
vetor de semaforos (permit). */
void* sign_extend_and_shift_left_imm(){
    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread da thread IR_read, para que a entrada e o
        sinal de controle e sinal de controle estejam corretos*/
        sem_wait(&permit[17]);

        // imm_extend recebe o valor extendido do Immediate (imm)
        imm_extend = (int) imm;
        // imm_extend_shift recebe o valor de imm_extend com 2 shifts para a esquerda
        imm_extend_shift = imm_extend << 2;

        // Realiza um sem_post() no semaforo que bloqueia o mux_ALUSrcB
        sem_post(&permit[13]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

/* Funcao que realiza o shift de duas posicoes para a esquerda e a concatenacao com o PC do valor do campo target(jump) de IR. 
O semaforo correspondente a esta funcao eh o de poiscao 18 no vetor de semaforos (permit). */
void* shift_left_target(){
    while(1){
        /* Execucao bloqueada ate que ocorra 1 sem_post() no semaforo correspondente
        a esta thread da thread IR_read, para que a entrada e o
        sinal de controle e sinal de controle estejam corretos*/
        sem_wait(&permit[18]);

        // jump_target_shift recebe o valor de jump_target com 2 shifts para a esquerda
        jump_target_shift = jump_target << 2;
        // jump_target_shift eh concatenado com PC[31..28]
        jump_target_shift = jump_target_shift | (PC & PcConcatenate); //concatencao com pc

        // Realiza um sem_post() no semaforo que bloqueia o mux_PCsource
        sem_post(&permit[14]);
        /*  Realiza um sem_post() no semaforo que bloqueia a main, para sincronizacao
        do clock logico. */
        sem_post(&sem_master);
    }
}

int main(int argc, char* argv[]){
    PC = 0;
    IR = 0;
    
    FILE *fp = fopen(argv[1], "r");

    bco_regs = (int*) calloc(32, sizeof(int));
    RAM = (char*) calloc(256, sizeof(char));

    // Le as instrucoes do arquivo e armazena no vetor que representa a RAM
    for(int i = 0; fscanf(fp, "%u", (unsigned int*)&RAM[i]) != EOF; i += 4);
    fclose(fp);

    int sem_initial = 0;
    pthread_t handle[THREADS]; //vetor de threads

    // Inicializa os semaforos
    for(int i = 0; i < THREADS; i++){
        sem_init(&permit[i], 0 , sem_initial);
    }

    /* Cria as threads */
    if(pthread_create(&handle[0], 0, (void*)control, NULL) != 0){
        printf("Error creating thread 0\n");
        exit(0);
    }

    if(pthread_create(&handle[1], 0, (void*)ALU, NULL) != 0){
        printf("Error creating thread 1\n");
        exit(0);
    }

    if(pthread_create(&handle[2], 0, (void*)memory_read, NULL) != 0){
        printf("Error creating thread 2\n");
        exit(0);
    }

    if(pthread_create(&handle[3], 0, (void*)ALUcontrol, NULL) != 0){
        printf("Error creating thread 3\n");
        exit(0);
    }

    if(pthread_create(&handle[4], 0, (void*)PC_write, NULL) != 0){
        printf("Error creating thread 4\n");
        exit(0);
    }

    if(pthread_create(&handle[5], 0, (void*)IR_write, NULL) != 0){
        printf("Error creating thread 5\n");
        exit(0);
    }

    if(pthread_create(&handle[6], 0, (void*)IR_read, NULL) != 0){
        printf("Error creating thread 6\n");
        exit(0);
    }

    if(pthread_create(&handle[7], 0, (void*)registers_read, NULL) != 0){
        printf("Error creating thread 7\n");
        exit(0);
    }

    if(pthread_create(&handle[8], 0, (void*)registers_write, NULL) != 0){
        printf("Error creating thread 8\n");
        exit(0);
    }

    if(pthread_create(&handle[9], 0, (void*)mux_IorD, NULL) != 0){
        printf("Error creating thread 9\n");
        exit(0);
    }

    if(pthread_create(&handle[10], 0, (void*)mux_RegDst, NULL) != 0){
        printf("Error creating thread 10\n");
        exit(0);
    }

    if(pthread_create(&handle[11], 0, (void*)mux_MemToReg, NULL) != 0){
        printf("Error creating thread 11\n");
        exit(0);
    }

    if(pthread_create(&handle[12], 0, (void*)mux_ALUsrcA, NULL) != 0){
        printf("Error creating thread 12\n");
        exit(0);
    }

    if(pthread_create(&handle[13], 0, (void*)mux_ALUsrcB, NULL) != 0){
        printf("Error creating thread 13\n");
        exit(0);
    }

    if(pthread_create(&handle[14], 0, (void*)mux_PCsource, NULL) != 0){
        printf("Error creating thread 14\n");
        exit(0);
    }

    if(pthread_create(&handle[15], 0, (void*)mux_BNE, NULL) != 0){
        printf("Error creating thread 15\n");
        exit(0);
    }

    if(pthread_create(&handle[16], 0, (void*)MDR_write, NULL) != 0){
        printf("Error creating thread 16\n");
        exit(0);
    }

    if(pthread_create(&handle[17], 0, (void*)sign_extend_and_shift_left_imm, NULL) != 0){
        printf("Error creating thread 17\n");
        exit(0);
    }

    if(pthread_create(&handle[18], 0, (void*)shift_left_target, NULL) != 0){
        printf("Error creating thread 18\n");
        exit(0);
    }

    if(pthread_create(&handle[19], 0, (void*)memory_write, NULL) != 0){
        printf("Error creating thread 19\n");
        exit(0);
    }

    // Loop da execucao do programa lido do arquivo. Cada iteracao do while representa um clock logico.
    while(1){
        ALUOut = ALUresult; //Escreve o valor do resultado de ALU em ALUout, no inicio de cada ciclo

        sem_post(&permit[0]); //inicializa a unidade de controle
        for(int i = 0; i < THREADS; i++){	//espera a finalizacao de todas as threads para iniciar um novo ciclo
            sem_wait(&sem_master);
        }
    }
}
