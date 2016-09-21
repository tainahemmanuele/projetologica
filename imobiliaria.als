module imobiliaria

one sig Imobiliaria{
     apartamentos: set Apartamento,
     lista: one ListaEspera

}

abstract sig Apartamento{
}

sig ApartamentoDoisQuartos extends Apartamento{
}{
	#ApartamentoDoisQuartos = 3
}

sig ApartamentoTresQuartos extends Apartamento{
}{
	#ApartamentoTresQuartos = 2
}

one sig Cobertura extends Apartamento{
}

sig ApartamentoAlugado in Apartamento{
}

sig Pessoa{
	alugado: one Apartamento
}

sig Pessoa50Anos in Pessoa{
}

one sig ListaEspera {
 	pessoas: set Pessoa
}

fact{
	all a: Apartamento | one a.~apartamentos
	all a: ApartamentoAlugado | one a.~alugado
	all p: Pessoa | one p.alugado => p.alugado in ApartamentoAlugado
}

pred MaiorIgual50[]{
}

pred show[]{
}

run show for 6
