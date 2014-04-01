module doar

// TEMPO
open util/ordering[Time] as to
sig Time{}

//SISTEMA
sig SistemaDoar {
	abrigos: set Abrigo
}

sig Abrigo {
	administracao : one Administrador,
	funcionarios : set Funcionario,
	animaisDoAbrigo : set Animal -> Time,
	clientes: set Cliente -> Time
}

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
	animaisAdotados: set Animal -> Time,
	idadeCliente: Int
}


sig Nome {}

sig Endereco{}

//ANIMAIS

abstract sig Animal {}

sig Cachorro extends Animal {
		racaCachorro: one RacaCachorro
}

sig Gato extends Animal {
	racaGato: one RacaGato
}

sig Passaro extends Animal {
	racaPassaro: one RacaPassaro
}

abstract sig Raca{}

sig RacaCachorro extends Raca{}

sig RacaGato extends Raca{}

sig RacaPassaro extends Raca{}

// FATOS
fact fatosSistema {
	#SistemaDoar = 1
	#Abrigo = 3
	all ab: Abrigo | #ab.funcionarios > 0 && #ab.funcionarios < 4
	all s: SistemaDoar | #s.abrigos = 3
	all a: Abrigo | 	#a.animaisDoAbrigo =< 4 // nao aceita
}

/*sig Node {adj: Node -> lone Int}
fact {
	all n: Node | let w = n.(n.adj) | some w => int[w] = 0
}*/

fact fatosPessoas {
	all c : Cliente | c.idadeCliente >= 16 // c.idadeCliente <= 100 
}

fact fatosAnimais {
	Animal = Cachorro + Gato + Passaro // animal = cachorro U gato U passaro
//	all a:Animal,t:Time | one a.~(animaisDoAbrigo.t)
	all ca: Cachorro | one ca.racaCachorro
	all ga: Gato | one ga.racaGato
	all pa: Passaro | one pa.racaPassaro
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some ab: Abrigo, an: Animal, c: Cliente |
				addAnimalAbrigo[ab, an, pre, pos] or
				addCliente[ab, c, pre, pos] or
				doaAnimal[ab, an, c, pre, pos] 
}

// Logica temporal

pred init[t: Time] {
	one SistemaDoar
	#Abrigo = 3
	#Administrador = 3
	no (Abrigo.clientes).t
	no (Abrigo.animaisDoAbrigo).t
}

pred addAnimalAbrigo[ab: Abrigo, an: Animal, t, t': Time] {
	an !in (ab.animaisDoAbrigo).t
	(ab.animaisDoAbrigo).t' = (ab.animaisDoAbrigo).t + an
} 

pred addCliente[ab: Abrigo, c: Cliente, t, t': Time] {
	c !in (ab.clientes).t
	(ab.clientes).t' = (ab.clientes).t + c
}

pred doaAnimal[ab: Abrigo, an: Animal, c: Cliente, t, t': Time] {
	an in (ab.animaisDoAbrigo).t
	c in (ab.clientes).t
	(ab.animaisDoAbrigo).t' = (ab.animaisDoAbrigo).t - an
	(c.animaisAdotados).t' = (c.animaisAdotados).t + an
}

// PREDICADOS e FUNCOES


// ASSERTS
assert todoAbrigoTemUmAdministrador {
	all a:Abrigo | one a.administracao
}

assert todoAbrigoTemPeloMenosUmFuncionario {
//fazer
}

check todoAbrigoTemUmAdministrador for 5

// main
pred show[]{}

run show for 5 but 10 Animal, 6 Funcionario

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
