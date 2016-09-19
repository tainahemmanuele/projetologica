module imobiliaria

sig Imobiliaria{
     apartamentos: set Apartamento
}

abstract sig Apartamento{
}

sig ApartamentoDoisQuartos extends Apartamento{
}


sig ApartamentoTresQuartos extends Apartamento{
}

sig ApartamentoAlugado in Apartamento{
}

sig Reserva{
}

sig Aluguel{
}

pred show[]{
}
run show for 3
