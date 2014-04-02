module doar

// TEMPO
open util/ordering[Time] as to
sig Time{}

//SISTEMA
sig SistemaDoar {
	abrigos: set Abrigo, 
	registros: set Registro -> Time,
	alertas: set Alerta -> Time
}

sig Abrigo {
	administracao : one Administrador,
	funcionarios : set Funcionario,
	animaisDoAbrigo : set Animal -> Time,
	clientes: set Cliente -> Time
}

sig Registro{}

sig Alerta{}

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
	idadeCliente: Idade
}

sig Idade{}

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
	all a: Abrigo | #a.animaisDoAbrigo =< 7
	all ab:Abrigo, t:Time | #Alerta <= #getAnimaisSemAbrigo[ab, t]
//	all rg : Registro, t : Time | one rg.~(registros.t)
//	all al : Alerta, t : Time | one al.~(alertas.t)
}

fact fatosPessoas {
	all i : Idade | one i.~idadeCliente
	all c: Cliente, t: Time | lone c.~(clientes.t)
	all n: Nome | one n.~nomeAdm || one n.~nomeCliente || one n.~nomeFunc
	all e: Endereco| one e.~endAdm || one e.~endCliente || one e.~endFunc
	all f: Funcionario | one f.~funcionarios
	all a: Administrador | one a.~administracao	
}

fact fatosAnimais {
	Animal = Cachorro + Gato + Passaro // animal = cachorro U gato U passaro
	all a:Animal,t:Time | 	(lone a.~(animaisDoAbrigo.t) and no(a.~(animaisAdotados.t))) or 
			(no a.~(animaisDoAbrigo.t) and lone a.~(animaisAdotados.t))
	all ca: Cachorro | one ca.racaCachorro
	all ga: Gato | one ga.racaGato
	all pa: Passaro | one pa.racaPassaro
	all rc: RacaCachorro | one rc.~racaCachorro
	all rg: RacaGato | one rg.~racaGato
	all rp: RacaPassaro | one rp.~racaPassaro

}


fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some sd: SistemaDoar, al: Alerta, rg: Registro, ab: Abrigo, an: Animal, c: Cliente |
				(addAnimalAbrigo[ab, an, pre, pos] and removeAlerta[sd, al, pre, pos]) or
				addCliente[ab, c, pre, pos] or
				(doaAnimal[ab, an, c, pre, pos] and removeAnimalDoAbrigo[ab, an,  pre, pos]) or
				addRegistro[sd, rg, pre, pos]
				
}

//FUNCOES

fun getAnimaisDoAbrigo[ab:Abrigo, t: Time]: set Animal{
	ab.(animaisDoAbrigo.t)
}


fun getClientesDoAbrigo[ab:Abrigo, t: Time]: set Cliente{
	ab.(clientes.t)
}

fun getAnimaisSemAbrigo[ab:Abrigo, t : Time] : set Animal {
	Animal - ab.(animaisDoAbrigo.t)
}

// Logica temporal

pred init[t: Time] {
	one SistemaDoar
	#Abrigo = 3
	#Administrador = 3
	no (SistemaDoar.registros).t
	no (SistemaDoar.alertas).t
	no (Abrigo.clientes).t
	no animaisAdotados.t
	no (Abrigo.animaisDoAbrigo).t
	no (Cliente.animaisAdotados).t
}
// PREDICADOS

pred addAnimalAbrigo[ab: Abrigo, an: Animal, t, t': Time] {
	an !in getAnimaisDoAbrigo[ab, t]
	getAnimaisDoAbrigo[ab, t'] = getAnimaisDoAbrigo[ab, t] + an
} 

pred addCliente[ab: Abrigo, c: Cliente, t, t': Time] {
	c !in getClientesDoAbrigo[ab, t]
	getClientesDoAbrigo[ab, t'] = getClientesDoAbrigo[ab, t] + c
}


pred doaAnimal[ab: Abrigo, an: Animal, c: Cliente, t, t': Time] {
	an in getAnimaisDoAbrigo[ab, t]
	c in getClientesDoAbrigo[ab, t]
	c in getClientesDoAbrigo[ab, t']
	(c.animaisAdotados).t' = (c.animaisAdotados).t + an
}

pred removeAnimalDoAbrigo[ab: Abrigo, an: Animal, t, t': Time]{
	an in getAnimaisDoAbrigo[ab, t]
	getAnimaisDoAbrigo[ab, t'] = getAnimaisDoAbrigo[ab, t] - an
}

pred addRegistro[sd: SistemaDoar, rg:Registro, t, t': Time]{
	rg not in (sd.registros).t
	(sd.registros).t' = (sd.registros).t + rg

}

pred removeAlerta[sd: SistemaDoar, al: Alerta , t,t':Time]{
	al in (sd.alertas).t
	(sd.alertas).t' = (sd.alertas).t - al
}



// ASSERTS
assert todoAbrigoTemUmAdministrador {
	all a:Abrigo | one a.administracao
}

assert todoAbrigoTemPeloMenosUmFuncionario {
	all a:Abrigo | #a.funcionarios > 0
}

assert animalAdotadoNaoPertenceANenhumAbrigo{
	all a:Animal, t:Time, ab:Abrigo, c:Cliente | a in ab.(animaisDoAbrigo.t) => a not in c.(animaisAdotados.t)
}

check todoAbrigoTemUmAdministrador for 5
check todoAbrigoTemPeloMenosUmFuncionario for 5
check animalAdotadoNaoPertenceANenhumAbrigo for 5

// main
pred show[]{}

run show for 5 but  3 Funcionario

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
