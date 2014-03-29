module doar

//SISTEMA
sig SistemaDoar {
	abrigos: set Abrigo
}

sig Abrigo {
	administracao : one Administrador,
	funcionarios : set Funcionario,
	animais : set Animal
}

// TEMPO
open util/ordering[Tempo] as to
sig Tempo{}

// PESSOAS
sig Administrador {
	nomeAdm: one Nome,
	endAdm: one Endereco
}

sig Funcionario {
	nomeFunc: one Nome,
	endFunc: one Endereco
}

sig Cliente {
	nomeCliente: one Nome,
	endCliente: one Endereco,
	idadeCliente: one Idade
}


sig Nome {}

sig Endereco{}

sig Idade{}



//ANIMAIS

abstract sig Animal {
}

sig Cachorro extends Animal {
}

sig Gato extends Animal {
}

sig Passaro extends Animal {
}

abstract sig Raca{}

sig RacaCachorro extends Raca{}

sig RacaGato extends Raca{}

sig RacaPassaro extends Raca{}

// FATOS
fact fatosSistema {
	#SistemaDoar = 1
	#Abrigo = 3
	all s: SistemaDoar | #s.abrigos = 3
	all a: Abrigo | 	#a.animais <= 4            // como fazer 400??
//	all a:Abrigo && all an1,an2: a.animais | an1 != an2
}

fact fatosPessoas {}

fact fatosAnimais {
	Animal = Cachorro + Gato + Passaro // animal eh cachorro U gato U passaro
}


// PREDICADOS e FUNCOES


// ASSERTS
assert todoAbrigoTemUmAdministrador {
	all a:Abrigo | one a.administracao
}


check todoAbrigoTemUmAdministrador for 5

pred show[]{}

run show for 5

//assinaturas (conjuntos e relações)
//fatos (invariantes)
//predicados e funções
//asserções
//run
//check

//Definição de 5 assinaturas, pelo menos uma herança
//Definição de 5 predicados e 3 funções
//Definição de 5 operações que simulam o comportamento temporal do sistema (usar assinatura Time)
//Definição e verificação de 3 asserts (testes sobre o sistema)
