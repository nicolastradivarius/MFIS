// El ejercicio propone averiguar qué día ocurrió cada ataque,
// el país de origen, el servidor afectado y el admin del servidor.

abstract sig Administrador {}

abstract sig Dia {}

abstract sig Servidor {
	admin: one Administrador
}

abstract sig Pais {}

sig Ataque {
	ocurrido: one Dia,
	origen: one Pais,
	objetivo: one Servidor
}

one sig Javier, Matias, Raul extends Administrador {}

one sig Lunes, Martes, Miercoles extends Dia {} 

one sig Osiris, Anubis, Isis extends Servidor {}

one sig Polonia, USA, Vietnam extends Pais {}

--------

fact "Hubo tres ataques" {#Ataque = 3}


fact "Cada servidor tiene un admin diferente" {
	// para cada admin ´a´
	all a: Administrador |
		// hay exactamente un servidor ´s´
		one s: Servidor |
			// para el cual ´a´ es el admin de ´s´ (se puede usar = por la multip)
			(a = s.admin)
}

fact "Cada ataque ocurrió en un día diferente" {
	// para cada combinación de ataques diferentes ´a1´ y ´a2´
	all disj a1, a2: Ataque |
		// ambos no ocurrieron el mismo día
		(a1.ocurrido != a2.ocurrido)
}


fact "Cada ataque vino de un pais distinto" {
	// no existe combinación de ataques distintos ´a1´ y ´a2´
	no disj a1, a2: Ataque |		
		// tal que su origen sea el mismo
		(a1.origen = a2.origen)
}

fact "Cada ataque fue dirigido a un servidor distinto" {
	// para cada combinacion de ataques ´a1´ y ´a2´
	all a1, a2: Ataque |
		// si son distintos ataques
		(a1 != a2) implies
			// entonces su objetivo fue un server diferente
			(a1.objetivo != a2.objetivo)
}

--------

fact "Lunes hubo ataque al server de Javier desde Polonia" {
	one a: Ataque |
		one s: Servidor |
			(a.ocurrido = Lunes) and 
			(a.origen = Polonia) and
			(s.admin = Javier) and
			(a.objetivo = s)
}

fact "Raul es administrador de Osiris" {
	one a: Administrador |
		(a = Raul) and (Osiris.admin = a)
}

fact "Matias es el admin de Anubis" {
	one s: Servidor |
		(s.admin = Matias)
}

fact "El miercoles hubo un ataque contra Anubis desde Vietnam" {
	one a: Ataque |
		(a.ocurrido = Miercoles) and
		(a.objetivo = Anubis) and
		(a.origen = Vietnam)
}

fact "A Raul le atacaron su servidor desde USA" {
	one a: Ataque |
		one s: Servidor |
			(s.admin = Raul) and
			(a.objetivo = s) and
			(a.origen = USA)
}

fact "El server de Raul fue atacado el día siguiente del ataque a Isis" {
	one disj a1, a2: Ataque |
		one disj s1, s2: Servidor |
			(s2 = Isis) and
			(s1.admin = Raul) and
			(a1.objetivo = s1) and
			(a2.objetivo = s2) and
			es_dia_siguiente[a1.ocurrido, a2.ocurrido]
}

pred es_dia_siguiente [d1, d2: Dia] {
	((d1 = Miercoles) and (d2 = Martes)) or
	((d1 = Martes) and (d2 = Lunes))
}


run {}

/*
	El ataque al servidor Osiris de Raúl ocurrió el día Martes y provino de USA
	El ataque al servidor Anubis de Matías ocurrió el día Miércoles y provino de Vietnam
	El ataque al servidor Isis de Javier ocurrió el día lunes y provino de Polonia
*/
