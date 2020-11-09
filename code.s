# codigo usado para o trab2 (SSC0112-Orgem 2018-1)
.data
salva:	.word 0    # nao usara essa alocacao em binario

.text
.globl main
	
executa:
	# jal main:				# vai ser necessario para o trabalho
	addi $t0, $zero, 10 	# nr maximo de iteracoes (10)
	addi $t1, $zero, 1  	# aux para incremento (1)
	addi $t2, $zero, 2  	# aux para nr 2

loop_exec1:
	beq $a0, $t0, sai_loop	# enquanto $a0 < $t0 => farah 10 iteracoes
	add $a0, $a0, $t1   # $a1 ++   no fim do loop $a0 terah 10
	sub $a2, $a2, $t1	# $a2 --   no fim do loop $a2 terah 2
	j loop_exec1

sai_loop:
	slt $t0, $a0, $t0 	# setando $t0 para zero  (como $a0==10 e $t0==10, entao $t0 = 0)

	addi $a3, $a2, 1	# $a3 = 3
	or 	$t3, $a3, $zero	# $t3 = 3

	addi $t4, $a3, 1	# $t4 = 4
	and  $t4, $t4, $a1  # $t4 = 4

	bne $t4, $t4, naopula	# nao efetiva o bne, pois $t4 == $t4  :-)

	la $t8, salva	#  sera substituida por addi
	sw $t2, 0($t8) # salva $t2 (tem vlr 2) na memoria

	lw $s2, 0($t8) # recupera vlr 2 para s2

naopula:
	jr $ra    # volta para a main
	
	#################################
	
main:
	andi $a0, $a0, 0		# $a0 tem todos os bits como 0
	addi $a1, $zero, -1  	# $a1 tem todos os bits como 1
	andi $a2, $a1, 12		# $a2 tem 12 para ser decrementado em executa
	
	la $t8, executa			# vai ser substituida por uma addi
	jalr $ra, $t8			# o SPIM inverte o rs com o rd para o jalr

	li $a0, 10				# exit nao vai para o binario do trab2
	syscall					# nao vai para o binario do trab2

	
##############################################
######  assembly simplificado para usar no trab2 
############################################## 
#                                   #&byte-&word comentarios
#			jal main				#00-00 fluxo para main  (&18, em hexa 12)
#executa: 	addi $t0, $zero, 10 	#04-01 nr maximo de iteracoes (10)
#			addi $t1, $zero, 1  	#08-02 aux para incremento (1)
#			addi $t2, $zero, 2  	#12-03 aux para nr 2
#loop_exec1:beq $a0, $t0, sai_loop	#16-04 enquanto $a0 < $t0 => farah 10 iteracoes   (desloca 3 palavras à frente)
#			add $a0, $a0, $t1   	#20-05 $a1 ++   no fim do loop $a0 terah 10
#			sub $a2, $a2, $t1		#24-06 $a2 --   no fim do loop $a2 terah 2
#			j loop_exec1			#28-07 volta para inicio do loop (desloca para instr no end a byte 16 ou palavra 04)
#sai_loop:	slt $t0, $a0, $t0 		#32-08 setando $t0 para zero  (como $a0==10 e $t0==10, entao $t0 = 0)
#			addi $a3, $a2, 1		#36-09 $a3 = 3
#			or 	$t3, $a3, $zero		#40-10 $t3 = 3
#			addi $t4, $a3, 1		#44-11 $t4 = 4
#			and  $t4, $t4, $a1  	#48-12 $t4 = 4
#			bne $t4, $t4, naopula	#52-13 nao efetiva o bne, pois $t4 == $t4  :-)    (desloca 3 palavras à frente)
#			addi $t8, $zero, 100	#56-14 carrega endereco para salvar na memoria
#			sw $t2, 0($t8) 			#60-15 salva $t2 (tem vlr 2) na memoria
#			lw $s2, 0($t8) 			#64-16 recupera vlr 2 para s2
#naopula:	jr $ra    				#68-17 fim de executa. Volta para a main.
#main:		andi $a0, $a0, 0		#72-18 $a0 tem todos os bits como 0
#			addi $a1, $zero, -1  	#76-19 $a1 tem todos os bits como 1
#			andi $a2, $a1, 12		#80-20 $a2 tem 12 para ser decrementado em executa
#			addi $t8, $zero, 4		#84-21 recupera endereco de executa (#04)
#			jalr $t8,$ra			#88-22 desvia fluxo para funcao executa
#									###### FIM da execução
#
##############################################################################################################################
## binario em DECIMAL, binario em HEXA, asm do bin; nr palavra: asm no source #comentario com posicao na mem em byte e em palavra)
############################################################################################################################## 
#201326610 0x0c000012  				jal 0x00000012 (&main/4) 		; 00: jal main				 #00-00 desvia fluxo para main  (&18, em hexa 12)
#537395210 0x2008000a  [executa:] 	addi $8, $0, 10       			; 01: addi $t0, $zero, 10 	 #04-01 nr maximo de iteracoes (10)
#537460737 0x20090001  				addi $9, $0, 1                  ; 02: addi $t1, $zero, 1  	 #08-02 aux para incremento (1)
#537526274 0x200a0002  				addi $10, $0, 2                 ; 03: addi $t2, $zero, 2  	 #12-03 aux para nr 2
#277348355 0x10880003  [loop_exec1:]beq $4, $8, 16 (sai_loop-20)/4  ; 04: beq $a0, $t0, sai_loop #16-04 enquanto $a0 < $t0 => farah 10 iteracoes   (desloca 3 palavras à frente)
#8986656   0x00892020  				add $4, $4, $9                  ; 05: add $a0, $a0, $t1   	 #20-05 $a1 ++   no fim do loop $a0 terah 10
#13185058  0x00c93022  				sub $6, $6, $9                  ; 06: sub $a2, $a2, $t1 	 #24-06 $a2 --   no fim do loop $a2 terah 2
#134217732 0x08000004  				j 0x00000004 (loop_exec1/4)     ; 07: j loop_exec1 		 	 #28-07 volta para inicio do loop (desloca 04 palavras para trás -04)
#8929322   0x0088402a  [sai_loop:]	slt $8, $4, $8       			; 08: slt $t0, $a0, $t0 	 #32-08 setando $t0 para zero  (como $a0==10 e $t0==10, entao $t0 = 0)
#549912577 0x20c70001  				addi $7, $6, 1                  ; 09: addi $a3, $a2, 1		 #36-09 $a3 = 3
#14702629  0x00e05825  				or $11, $7, $0                  ; 10: or 	$t3, $a3, $zero  #40-10 $t3 = 3
#552337409 0x20ec0001  				addi $12, $7, 1                 ; 11: addi $t4, $a3, 1		 #44-11 $t4 = 4
#25518116  0x01856024  				and $12, $12, $5                ; 12: and  $t4, $t4, $a1  	 #48-12 $t4 = 4
#361496579 0x158c0003  				bne $12, $12, 16 (naopula-56)/4 ; 13: bne $t4, $t4, naopula	 #52-13 nao efetiva o bne, pois $t4 == $t4  :-)    (desloca 3 palavras à frente)
#538443876 0x20180064  				addi $24, $0, 100               ; 14: addi $t8, $zero, 100	 #56-14 carrega endereco para salva na memoria
#2936668160 0xaf0a0000  			sw $10, 0($24)                  ; 15: sw $t2, 0($t8) 		 #60-15 salva $t2 (tem vlr 2) na memoria
#2400321536 0x8f120000  			lw $18, 0($24)                  ; 16: lw $s2, 0($t8) 	  	 #64-16 recupera vlr 2 para s2
#1407188992 0x53E00000 [naopula:]	jr $31                			; 17: jr $ra    			 #68-17 fim de executa. Volta para a main.   0101 0011 1110 0000 0000 0000 0000 0000 (0x53E00000) 
#813957120 0x30840000  [main:]		andi $4, $4, 0           		; 18: andi $a0, $a0, 0		 #72-18 $a0 tem todos os bits como 0
#537264127 0x2005ffff  				addi $5, $0, -1                 ; 19: addi $a1, $zero, -1    #76-19 $a1 tem todos os bits como 1
#816185356 0x30a6000c  				andi $6, $5, 12                 ; 20: andi $a2, $a1, 12	 	 #80-20 $a2 tem 12 para ser decrementado em executa
#538443780 0x20180004  				addi $24, $0, 4                 ; 21: addi $t8, $zero, 4	 #84-21 recupera endereco de executa (#04)
#1461649408 0x571f0000  			jalr $24, $31                   ; 22: jalr $t8, $ra 	 	 #88-22 desvia fluxo para funcao executa  010101 11000 11111 0000 0000 0000 0000 (0x571f0000)
#4294967295 0xffffffff				instrução invalida              ; 23: instrucao invalida     #92-23 instrucao invalida 1111 1111 1111 1111 1111 1111 1111 1111 (0xffffffff)
