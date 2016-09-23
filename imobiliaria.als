module imobiliaria
--open util/ordering[Time]

one sig Imobiliaria{
     apartamentosAlugados: set Apartamento, --colocar Time aqui
	apartamentosDisponiveis: set Apartamento,
     lista: one ListaEspera --colocar Time aqui

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
    alugado: lone Apartamento
}

sig Pessoa50Anos in Pessoa{
}

--sig Grupo{
	--integrantes: some Pessoa,
	--alugado: Apartamento 
--}

one sig ListaEspera {
 	pessoas: set Pessoa
}

sig Time {
}

fact{
	#ApartamentoDoisQuartos = 3
	#ApartamentoTresQuartos = 2
	#Imobiliaria.apartamentosAlugados + #Imobiliaria.apartamentosDisponiveis = 6
	
	all a: Imobiliaria.apartamentosAlugados | some a.~alugado

	all p: Pessoa | (p !in ListaEspera.pessoas) => (one p.alugado => p.alugado in Imobiliaria.apartamentosAlugados)
	!TodosAlugados => no ListaEspera.pessoas
	all p: Pessoa| (p.alugado in Cobertura) => (p in Pessoa50Anos)
	all p: Pessoa | no p.alugado => p in ListaEspera.pessoas
    all p: ListaEspera.pessoas | no p.alugado
    all a: ApartamentoDoisQuartos | #a.~alugado <= 2
	all a: ApartamentoTresQuartos | #a.~alugado <= 3
    all c :Cobertura | #c.~alugado <= 3
    all a: Apartamento | apCheio[a] => a in Imobiliaria.apartamentosAlugados
    all a: Apartamento | a in Imobiliaria.apartamentosAlugados => a ! in Imobiliaria.apartamentosDisponiveis
	
}

pred apCheio[a:Apartamento]{
	a in ApartamentoDoisQuartos => #a.~alugado = 2 and 
	a in ApartamentoTresQuartos => #a.~alugado = 3
 
}

--pred init[t:Time]{
	--no (Grupo.alugado).t
--}

--fact traces{
--	init[first]
--	all pre: Time - last | let pos = pre.next | pos = pre.next
--}

pred TodosAlugados[]{
	all a: Apartamento | a in Imobiliaria.apartamentosAlugados
}

--pred Aluga[g: Grupo, a: Apartamento, t,t': Time]{ -- verificar o tamanho do grupo para cada tipo de ap
--	a !in ApartamentoAlugado
--	no g.alugado.t
--	g.alugado.t' = a
--	a in ApartamentoAlugado
--}

--pred Desaluga[g: Grupo, t,t': Time]{
--	one g.alugado.t
--	no g.alugado.t'
--	g.alugado.t !in ApartamentoAlugado
--}

pred show[]{
}

run show for 20
