module imobiliaria
open util/ordering[Time]

one sig Imobiliaria{
	apartamentosAlugados: Apartamento -> Time,
	apartamentosDisponiveis: Apartamento -> Time,
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



sig Pessoa{
	--alugado: lone Apartamento
}

sig Pessoa50Anos in Pessoa{
}

sig Grupo{
	integrantes: some Pessoa,
	alugado: Apartamento -> Time 
}

one sig ListaEspera {
 	grupos: Grupo -> Time 
}

sig Time {
}

fact{
	#ApartamentoDoisQuartos = 3
	#ApartamentoTresQuartos = 2
	#Cobertura = 1
	
	all g: Grupo | all t: Time | lone (g.alugado).t
	all a: Apartamento, t: Time | lone a.(~(alugado.t))
	all p: Pessoa | #p.~integrantes = 1
	all g: Grupo | all t: Time | some (g.alugado).t <=> g !in espera[t]

	-- Estes 2 fatos deveriam servir pra contornar os dois comentados abaixo, mas não o fazem, a.~alugado.t não funciona
	-- pois a relação é ternaria.
	all g: Grupo, t: Time | one (g.alugado).t => (g.alugado).t in (Imobiliaria.apartamentosAlugados).t
	all a: Apartamento, t: Time | (a in (Imobiliaria.apartamentosDisponiveis).t or a in (Imobiliaria.apartamentosAlugados).t) and
		 (!(a in (Imobiliaria.apartamentosDisponiveis).t and a in (Imobiliaria.apartamentosAlugados).t))
	--all a: Apartamento | all t: Time | no (a.~alugado).t <=> a in (Imobiliaria.apartamentosDisponiveis).t
	--all a: Apartamento | all t: Time | one (a.~alugado).t <=> a in (Imobiliaria.apartamentosAlugados).t

	all g: Grupo | all t: Time | (g.alugado).t in Cobertura <=> g.integrantes in Pessoa50Anos
}

--pred apCheio[a:Apartamento]{
--	a in ApartamentoDoisQuartos => #a.~alugado = 2 and 
--	a in ApartamentoTresQuartos => #a.~alugado = 3
 
--}

fun espera[t: Time]: set Grupo {
	((Imobiliaria.lista).grupos).t
}

pred init[t:Time]{
	no (Grupo.alugado).t and
	all a: Apartamento | a in (Imobiliaria.apartamentosDisponiveis).t
	all a: Apartamento | a !in (Imobiliaria.apartamentosAlugados).t
}

fact traces{
	init[first]
	all pre: Time - last | let pos = pre.next | 
		some g: Grupo, a:Apartamento |
			aluga[g, a, pre, pos] or
			desaluga[g, a, pre, pos]
}

pred comunsAlugados[t: Time]{
	all a: Apartamento - Cobertura | a in (Imobiliaria.apartamentosAlugados).t
}

pred aluga[g: Grupo, a: Apartamento, t,t': Time]{ --verificar o tamanho do grupo para cada tipo de ap
	a in (Imobiliaria.apartamentosDisponiveis).t and
	no (g.alugado).t and
	(g.alugado).t' = a and
	a in (Imobiliaria.apartamentosAlugados).t'
}

pred desaluga[g: Grupo, a: Apartamento, t,t': Time]{  --verificar o tamanho do grupo para cada tipo de ap
	a in (Imobiliaria.apartamentosAlugados).t and
	(g.alugado).t = a and
	no (g.alugado).t' and
	a in (Imobiliaria.apartamentosDisponiveis).t'
}

pred show[]{
	all g: Grupo | #g.integrantes <= 3
}

run show for 10 but 20 Pessoa
