module doar

// TEMPO
open util/ordering[Tempo] as to
sig Tempo{}

//SISTEMA
sig SistemaDoar {
	abrigos: set Abrigo
}

sig Abrigo {
	administracao : one Administrador,
	funcionarios : set Funcionario,
	animais : set Animal -> Tempo,
	clientes: set Cliente -> Tempo
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
	idadeCliente: Int
}


sig Nome {}

sig Endereco{}


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
	all a: Abrigo | 	#a.animais =< 100 
//	all a:Abrigo && all an1,an2: a.animais | an1 != an2
}

fact fatosPessoas {}

fact fatosAnimais {
	Animal = Cachorro + Gato + Passaro // animal = cachorro U gato U passaro
}

fact idadeCliente {
	all c : Cliente |
	c.idadeCliente >= 18 and
	c.idadeCliente <= 120
} 

// Eventos com Cliente

pred init[t:Tempo] {
	no (Abrigo.clientes).t
}

abstract sig clienteEvent {
	a : Abrigo,
	c : Cliente,
	t, t' : Tempo 
}

abstract sig addCliente extends clienteEvent {} {
	c !in (a.clientes).t
	(a.clientes).t' =  (a.clientes).t + c
} 

abstract sig removeCliente extends clienteEvent {} {
	c in (a.clientes).t
	(a.clientes).t' = (a.clientes).t - c
}

fact traceCliente {
	init[to/first]
	all pre: Tempo-last | let pos = pre.next |
		some e: clienteEvent {
			e.t = pre and e.t' = pos
			((e in addCliente) or
			   (e in removeCliente))
		} 
}

// PREDICADOS e FUNCOES

// ASSERTS
assert todoAbrigoTemUmAdministrador {
	all a:Abrigo | one a.administracao
}

check todoAbrigoTemUmAdministrador for 5

pred show[]{}

run show for 3 but 2 Cliente

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
