module imobiliaria

one sig Imobiliaria{
     apartamentos: set Apartamento,
     lista: one ListaEspera

}

abstract sig Apartamento{
}

sig ApartamentoDoisQuartos extends Apartamento{
}

sig ApartamentoTresQuartos extends Apartamento{
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
	#ApartamentoDoisQuartos = 3
	#ApartamentoTresQuartos = 2
	all a: Apartamento | one a.~apartamentos
	all a: ApartamentoAlugado | one a.~alugado
	all p: Pessoa | (p !in ListaEspera.pessoas) && (one p.alugado => p.alugado in ApartamentoAlugado)
	!TodosAlugados => no ListaEspera.pessoas
	all p: Pessoa | (p.alugado in Cobertura) => (p in Pessoa50Anos)
}

pred TodosAlugados[]{
	all a: Apartamento | a in ApartamentoAlugado
}

pred MaiorIgual50[l: ListaEspera]{
	l.pessoas in Pessoa50Anos
}

pred Aluga[p: Pessoa, a: Apartamento]{
	a !in ApartamentoAlugado
	p.alugado = a
	a in ApartamentoAlugado
}

pred Despeja[p: Pessoa]{
	p.alugado in ApartamentoAlugado
	no p.alugado
	p.alugado !in ApartamentoAlugado
}

pred AddListaEspera[p: Pessoa, l: ListaEspera] {
	p !in l.pessoas
	l.pessoas = l.pessoas + p
}

pred RemoveListaEspera[p: Pessoa, l: ListaEspera] {
	p in l.pessoas
	l.pessoas = l.pessoas - p
}

pred show[]{
}

run show for 6
