module imobiliaria
open util/ordering[Time]

one sig Imobiliaria{
	apartamentosAlugados: Apartamento -> Time,
	apartamentosDisponiveis: Apartamento -> Time,
	lista: one ListaEspera

}

abstract sig Apartamento{
	inquilinos: Grupo -> Time
}

sig ApartamentoDoisQuartos extends Apartamento{
}

sig ApartamentoTresQuartos extends Apartamento{
}

one sig Cobertura{
	--inquilinos: Grupo -> Time
	ap: ApartamentoTresQuartos
}



 sig Pessoa{
	--alugado: lone Apartamento
}

sig Pessoa50Anos in Pessoa{
}



sig Grupo{
	integrantes: some Pessoa,

}

one sig ListaEspera {
 	grupos: Grupo -> Time 
}

sig Time {
}

fact{
	#ApartamentoDoisQuartos = 3
	#ApartamentoTresQuartos = 3
	#Cobertura = 1
	

	--a.(~(alugado.t))
	all g: Grupo | all t: Time | lone g.(~(inquilinos.t))
	all a: Apartamento, t: Time | lone a.inquilinos.t
	all p: Pessoa | #p.~integrantes = 1
	all g: Grupo | all t: Time | some g.(~(inquilinos.t)) => g !in espera[t]


	all a: Apartamento | all t: Time | no a.inquilinos.t <=> a in (Imobiliaria.apartamentosDisponiveis).t
	all a: Apartamento | all t: Time | one a.inquilinos.t <=> a in (Imobiliaria.apartamentosAlugados).t

	--all g: Grupo | all t: Time | (g.alugado).t in Cobertura and g.integrantes in Pessoa50Anos => one Cobertura
    some g: Grupo | all t: Time |apartamentoAlugado[g,t] in Cobertura.ap => apartamentoAlugado[g,t].inquilinos.t.integrantes in Pessoa50Anos
	all a: Apartamento,  g:Grupo, t:Time | (a in Cobertura.ap) and (a in Imobiliaria.apartamentosAlugados.t) =>  apartamentoAlugado[g,t].inquilinos.t.integrantes in Pessoa50Anos

}

fun apartamentoAlugado[g: Grupo, t:Time]: lone Apartamento{
	g.(~(inquilinos.t))

}


fun espera[t: Time]: set Grupo {
	((Imobiliaria.lista).grupos).t
}

pred init[t:Time]{
	no (Apartamento.inquilinos).t and
	no espera[t] and
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
	all a: Apartamento - Cobertura.ap | a in (Imobiliaria.apartamentosAlugados).t
}

pred aluga[g: Grupo, a: Apartamento, t,t': Time]{ --verificar o tamanho do grupo para cada tipo de ap
	a in (Imobiliaria.apartamentosDisponiveis).t and
	((a in ApartamentoDoisQuartos and #g.integrantes = 2) or (a in ApartamentoTresQuartos + Cobertura and #g.integrantes = 3)) and
	(a in Cobertura.ap => comunsAlugados[t] and g.integrantes in Pessoa50Anos ) and
	no a.inquilinos.t and
	a.inquilinos.t' = g and
	a in (Imobiliaria.apartamentosAlugados).t'
}

pred desaluga[g: Grupo, a: Apartamento, t,t': Time]{  --verificar o tamanho do grupo para cada tipo de ap
	a in (Imobiliaria.apartamentosAlugados).t and
	a.inquilinos.t = g and
	no a.inquilinos.t' and
	a in (Imobiliaria.apartamentosDisponiveis).t'
}

pred show[]{
	  all g: Grupo | #g.integrantes <= 3
	 --no Pessoa50Anos
	some t:Time | one Cobertura.ap.inquilinos.t 
}

run show for 10 but 20 Pessoa
