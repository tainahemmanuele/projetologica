module imobiliaria

sig Imobiliaria{
     apartamentos: set Apartamento
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

sig ApartamentoAlugado in Apartamento{
}

sig Reserva{
}

sig Aluguel{
}

sig Pessoa{
	alugado: one Apartamento
}

sig Pessoa50anos in Pessoa{
}

fact{
	all a: Apartamento | one a.~apartamentos
	all a: ApartamentoAlugado | one a.~alugado
	all p: Pessoa | one p.alugado => p.alugado in ApartamentoAlugado
}

pred show[]{
}

run show for 5
