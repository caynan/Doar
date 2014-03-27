module doar

sig Abrigo {
	administracao : one Administrador,
	funcionarios : set Funcionario,
	animais : set Animal
}

sig Administrador {
}

sig Funcionario {
}

sig Animal {
}

sig Cadastrado {
}

// extends ou in??
sig Cachorro extends Animal {
}

sig Gato extends Animal {
}

sig Passaro extends Animal {
}

fact fatos {

	#Abrigo = 3
	all a: Abrigo | maxAnimais[a]

	Animal = Cachorro + Gato + Passaro // animal eh cachorro U gato U passaro
}

pred maxAnimais[a:Abrigo] {
	#a.animais <= 4 // como fazer 400??
}

assert todoAbrigoTemUmAdministrador {
	all a:Abrigo | one a.administracao
}

check todoAbrigoTemUmAdministrador for 5

pred show[]{}

run show for 2

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
