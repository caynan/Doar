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
	endereco: one Endereco,
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
	idadeCliente: Idade
}

sig Idade{}

sig Nome {}

sig Endereco{
	bairro: one Bairro
}

// bairros e suas instancias.
abstract sig Bairro {}

one sig AltoBranco extends Bairro {}
one sig Bodocongo extends Bairro {}
one sig Prata extends Bairro {}

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

fact fatosPessoas {}

fact fatosAnimais {
	Animal = Cachorro + Gato + Passaro // animal = cachorro U gato U passaro
//	all a:Animal,t:Time | one a.~(animaisDoAbrigo.t)
	all ca: Cachorro | one ca.racaCachorro
	all ga: Gato | one ga.racaGato
	all pa: Passaro | one pa.racaPassaro
}

// um animal deve ser unico
fact animalUnico {
	all ab1: Abrigo, ab2: Abrigo, cl1: Cliente, cl2: Cliente, an: Animal,  t: Time | 
		cadaAnimalEmAbrigoDiferente[ab1, ab2, an, t]  and
		cadaAnimalTemUmUnicoDono[cl1, cl2, an, t]
}

// Animal deve estar em um unico abrigo.
pred cadaAnimalEmAbrigoDiferente[ab1: Abrigo, ab2: Abrigo, an: Animal, t: Time]{
	(ab1 != ab2) => (an in (ab1.animaisDoAbrigo).t => an !in (ab2.animaisDoAbrigo).t)
}

// Animal deve possuir um unico dono
pred cadaAnimalTemUmUnicoDono[cl1: Cliente, cl2: Cliente, an: Animal, t: Time]{
	(cl1 != cl2) => (an in (cl1.animaisAdotados).t => an !in (cl2.animaisAdotados).t)
}
// Funcionario deve ser unico por abrigo (um mesmo funcionario n deve estar em dois abrigos)
fact funcionarioUnico {
	all ab1: Abrigo, ab2: Abrigo, f:Funcionario | cadaFuncionarioEmAbrigoDiferente[ab1, ab2, f]
}

pred cadaFuncionarioEmAbrigoDiferente[ab1: Abrigo, ab2: Abrigo, f: Funcionario]{
	(ab1 != ab2) => (f in ab1.funcionarios => f !in ab2.funcionarios)
}

// Administrador deve ser unico por abrigo (um mesmo administrador, n deve estar em dois abrigos)
fact AdministradorUnico {
	all ab1: Abrigo, ab2: Abrigo, ad: Administrador | cadaAdministradorEmAbrigoDiferente[ab1, ab2, ad]
}

pred cadaAdministradorEmAbrigoDiferente[ab1: Abrigo, ab2: Abrigo, ad: Administrador]{
	(ab1 != ab2) => (ad in ab1.administracao => ad !in ab2.administracao)
}


// Logica temporal
fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some ab: Abrigo, an: Animal, c: Cliente |
				addAnimalAbrigo[ab, an, pre, pos] or
				addCliente[ab, c, pre, pos] or
				adotaAnimal[ab, an, c, pre, pos] 
}

pred init[t: Time] {
	one SistemaDoar
	#Abrigo = 3
	#Administrador = 3
	no (Abrigo.clientes).t
	no (Abrigo.animaisDoAbrigo).t
}

// Adicionar novo animal ao abrigo
pred addAnimalAbrigo[ab: Abrigo, an: Animal, t, t': Time] {
	an !in (ab.animaisDoAbrigo).t
	(ab.animaisDoAbrigo).t' = (ab.animaisDoAbrigo).t + an
} 

// Adicionar novo cliente ao abrigo
pred addCliente[ab: Abrigo, c: Cliente, t, t': Time] {
	c !in (ab.clientes).t
	(ab.clientes).t' = (ab.clientes).t + c
}

// Cliente adota animal
pred adotaAnimal[ab: Abrigo, an: Animal, c: Cliente, t, t': Time] {
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
	all a:Abrigo | some a.funcionarios
}

//check todoAbrigoTemUmAdministrador for 5

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
