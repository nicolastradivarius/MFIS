/**
Considere un puente levadizo sobre el que pasan autos cuando se encuentra bajo, permitiendo
tambien el paso de barcos (por debajo de el) cuando se encuentra elevado. Considere que en toda
instancia deben existir al menos dos barcos y al menos dos autos. Por cuestiones de seguridad, en
todo momento puede haber como maximo un auto sobre el puente.
*/

open util/ordering[Estado] as ord

sig Barco { }

sig Auto { }

abstract sig Puente { }

one sig Elevado, Bajo extends Puente { }

sig Estado {
	puente: one Puente,
	barcosEnEspera: set Barco,
	autosEnEspera: set Auto,
	autosEnPuente: lone Auto
}

fact "en toda instancia hay al menos dos autos y dos barcos" {
	#Auto >= 2 and #Barco >= 2
}

--------------------------- Dinámica ---------------------------

/**
Agregar los predicados y/o facts necesarios para modelar la dinámica del problema. Considere
que los cambios de estados se producen porque:

* Llega un barco al puente
* Llega un auto al puente 
* Sube un auto al puente (el puente debe estar bajo)
* Baja un auto del puente (el auto debe estar en el puente)
* Cruza un barco (el puente debe estar elevado y el barco debe estar esperando)
* Cambia la posición del puente (cambia de elevado a bajo o de bajo a elevado)

Estas acciones deben ser disjuntas, es decir, los cambios de estados se producen por la ocurrencia
de solo una de ellas. Escriba la especificación para que así sea.

Entre los predicados que defina deberá considerar necesariamente predicados para:

* Expresar cuándo un estado es válido. (Observación: En caso de optar por no definir 
un predicado para esto deberá dejarse registro, explícitamente, de qué parte del modelo 
captura la especificación de las condiciones que caracterizan estados válidos)
* Expresar cada acción posible
*/

fact estados_validos {
	all e: Estado | 
		// si el puente está elevado, no puede haber autos sobre él.
		((e.puente = Elevado) implies (no e.autosEnPuente)) and
		// no hay un mismo auto en el puente y esperando al mismo tiempo.
		(no e.autosEnEspera & e.autosEnPuente)
}

// el puente empieza Bajo, no hay ningún auto ni barco esperando.
pred init [e: Estado] {
	(e.puente = Bajo) and (no e.barcosEnEspera) and (no e.autosEnEspera) and (no e.autosEnPuente)
}

fact traces {
	all e1: Estado - ord/last | let e2 = e1.next |
		init [ord/first] and (
			transicion1[e1, e2] or
			transicion2[e1, e2] or
			transicion3[e1, e2] or
			transicion4[e1, e2] or
			transicion5[e1, e2] or
			transicion6[e1, e2]
		)
}

pred llegaBarco [e1, e2: Estado] {
	some b: Barco |
		(b not in e1.barcosEnEspera) and
//		(b in e2.barcosEnEspera) and
		(e2.barcosEnEspera = e1.barcosEnEspera + b) and
		-- marco
		(e2.autosEnEspera = e1.autosEnEspera) and
		(e2.autosEnPuente = e1.autosEnPuente) and
		(e2.puente = e1.puente)
}

pred llegaAuto [e1, e2: Estado] {
	some a: Auto |
		(a not in e1.autosEnEspera) and
//		(a in e2.autosEnEspera) and
		(e2.autosEnEspera = e1.autosEnEspera + a) and
		-- marco
		(e2.barcosEnEspera = e1.barcosEnEspera) and
		(e2.autosEnPuente = e1.autosEnPuente) and
		(e2.puente = e1.puente)
}

// Sube un auto al puente (el puente debe estar bajo)
pred subeAuto [e1, e2: Estado] {
	some a: Auto |
		(e1.puente = Bajo) and
		(a in e1.autosEnEspera) and
//		(a in e2.autosEnPuente) and
		(e2.autosEnPuente = e1.autosEnPuente + a) and
		(e2.autosEnEspera = e1.autosEnEspera - a) and
		-- marco
		(e2.barcosEnEspera = e1.barcosEnEspera) and
		(e2.puente = e1.puente)
}

// Baja un auto del puente (el auto debe estar en el puente)
pred bajaAuto [e1, e2: Estado] {
	some a: Auto |
		(a in e1.autosEnPuente) and
		(e2.autosEnPuente = e1.autosEnPuente - a) and
		-- marco
		(e2.autosEnEspera = e1.autosEnEspera) and
		(e2.barcosEnEspera = e1.barcosEnEspera) and
		(e2.puente = e1.puente)
}

// Cruza un barco (el puente debe estar elevado y el barco debe estar esperando)
pred cruzaBarco [e1, e2: Estado] {
	some b: Barco | 
		(e1.puente = Elevado) and
		(b in e1.barcosEnEspera) and
//		(b not in e2.barcosEnEspera) and
		(e2.barcosEnEspera = e1.barcosEnEspera - b) and
		-- marco
		(e2.autosEnEspera = e1.autosEnEspera) and
		(e2.puente = e1.puente)
}

// Cambia la posición del puente (cambia de elevado a bajo o de bajo a elevado)
pred cambiaPuente [e1, e2: Estado] {
	(no e1.autosEnPuente) and
	(e1.puente = Bajo implies e2.puente = Elevado) and
	(e1.puente = Elevado implies e2.puente = Bajo) and
	-- marco
	(e2.autosEnEspera = e1.autosEnEspera) and
	(e2.barcosEnEspera = e1.barcosEnEspera) and
	(e2.autosEnPuente = e1.autosEnPuente)
}

---------------------- transiciones disjuntas -------------------------

pred transicion1 [e1, e2: Estado] {
	llegaBarco[e1, e2] and not (
		llegaAuto[e1, e2] or 
		subeAuto[e1, e2] or 
		bajaAuto[e1, e2] or 
		cruzaBarco[e1, e2] or
		cambiaPuente[e1, e2]
	)
}

pred transicion2 [e1, e2: Estado] {
	llegaAuto[e1, e2] and not (
		llegaBarco[e1, e2] or 
		subeAuto[e1, e2] or 
		bajaAuto[e1, e2] or 
		cruzaBarco[e1, e2] or
		cambiaPuente[e1, e2]
	)
}

pred transicion3 [e1, e2: Estado] {
	subeAuto[e1, e2] and not (
		llegaAuto[e1, e2] or 
		llegaBarco[e1, e2] or 
		bajaAuto[e1, e2] or 
		cruzaBarco[e1, e2] or
		cambiaPuente[e1, e2]
	)
}

pred transicion4 [e1, e2: Estado] {
	bajaAuto[e1, e2] and not (
		llegaAuto[e1, e2] or 
		subeAuto[e1, e2] or 
		llegaBarco[e1, e2] or 
		cruzaBarco[e1, e2] or
		cambiaPuente[e1, e2]
	)
}

pred transicion5 [e1, e2: Estado] {
	cruzaBarco[e1, e2] and not (
		llegaAuto[e1, e2] or 
		subeAuto[e1, e2] or 
		bajaAuto[e1, e2] or 
		llegaBarco[e1, e2] or
		cambiaPuente[e1, e2]
	)
}


pred transicion6 [e1, e2: Estado] {
	cambiaPuente[e1, e2] and not (
		llegaAuto[e1, e2] or 
		subeAuto[e1, e2] or 
		bajaAuto[e1, e2] or 
		llegaBarco[e1, e2] or
		cruzaBarco[e1, e2]
	)
}



run default {} for 9

// un barco llega cuando el puente está elevado y cruza
run $1 {
	some e1, e3: Estado - ord/last | let e2 = e1.next | let e4 = e3.next |
		e1.puente = Elevado and
		// forzamos a que la sucesión sea en 3 estados continuos en lugar de 2 y 2 separados.
		e2 = e3 and
		// forzamos a que el barco que llega sea el mismo que cruza
		(some b: e2.barcosEnEspera | b not in e4.barcosEnEspera) and
		transicion1[e1, e2] and transicion5[e3, e4]
		
} for 9

// un auto llega, espera a que cruza un barco, y luego cruza él.
run $2 {
	some e1, e3: Estado - ord/last | let e2 = e1.next | let e4 = e3.next |
		e3 in e1.nexts and
		transicion2[e1, e2] and transicion5[e2, e3] and 
		transicion6[e3, e4] and transicion3[e4, e4.next]
} for 9



// Si hay un auto en el puente, puede mantenerse sobre el puente en forma indeterminada.
// Si el estado elegido es el primero, el analizador no encuentra instancias para este caso, 
// y es intencional, porque si un auto está en el puente, las únicas transiciones posibles son que
// lleguen barcos, lleguen autos, o el auto cruce el puente.
// Si el estado es cualquiera menos el último, el analizador encuentra instancias ya que
// es posible que en esas instancias, lo único que suceda es que lleguen barcos o autos mientras
// el auto se mantiene en el puente hasta el último estado.
run autoPermaneceEnPuente {
	some e1: Estado | 
--		e1 = ord/first and
		(e1 = ord/first.next) and
--		(e1 != ord/last) and
		(some e1.autosEnPuente) and
		(all e1sigs: e1.nexts | (some e1sigs.autosEnPuente & e1.autosEnPuente))
} for 5

// El puente siempre estará `bajo` en el estado inmediatamente siguiente de aquel 
// en el cual hay algún auto sobre el puente.
// El analizador no encuentra contraejemplos.
check puenteSiempreBaja {
	all e1: Estado-ord/last | let e2 = e1.next | 
		(some e1.autosEnPuente) implies (e2.puente = Bajo)
} for 15

