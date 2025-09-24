/*
Considere un puente levadizo sobre el que pasan autos cuando se encuentra bajo, permitiendo
también el paso de barcos (por debajo de él) cuando esta elevado. Considere que en toda
instancia deben existir al menos dos barcos y al menos dos autos. Por seguridad, en
todo momento puede haber como máximo un auto sobre el puente.
*/

open util/ordering[Estado]

sig Barco { }

sig Auto { }

abstract sig EstadoPuente { }

one sig Elevado, Bajo extends EstadoPuente { }

sig Estado {
	puente: one EstadoPuente,
	// cambio de some a set para no forzar que siempre haya barcos esperando.
	barcosEnEspera: set Barco,
	autosEnEspera: set Auto,
	// cambio de one a lone para permitir que el puente este vacio.
	autosEnPuente: lone Auto
}

// Agregamos este hecho para solucionar el problema evidenciado por el check de 
// autoEsperandoYEnPuente del archivo anterior.
fact "no hay un mismo auto cruzando el puente y esperando para cruzarlo" {
	no autosEnPuente & autosEnEspera
}

// Agregamos este hecho en respuesta al run de autosEnPuenteElevado del archivo anterior.
fact "no hay autos cruzando el puente cuando este esta elevado" {
	no e: Estado | e.puente = Elevado and some e.autosEnPuente
}

fact "si el puente esta elevado, ningun auto puede avanzar su trayectoria" {
	all e1: Estado - last | let e2 = e1.next | 
		(e1.puente = Elevado) implies 
			(e2.autosEnEspera = e1.autosEnEspera)
}

/*
Me prioriza indirectamente que el auto sobre el puente baje en el estado siguiente.
Esto sucede porque estoy exigiendo que el auto haya estado en espera en el estado anterior
para que pueda estar sobre el puente en el estado actual. Si quisiese que un auto este en
el puente durante dos estados seguidos, se violaria este hecho porque el estado anterior
seria tal que el auto no esta en espera, sino en el puente.
fact "todo auto que suba al puente debe haber estado esperando inmediatamente antes" {
	all e1: Estado - last, a: Auto | let e2 = e1.next |
		(a in e2.autosEnPuente) implies (a in e1.autosEnEspera)
}
*/

run default {}

// chequeamos que no haya un auto esperando y en el puente al mismo tiempo.
// No encuentra contraejemplos.
check autoEsperandoYEnPuente {
	all e: Estado| e.autosEnEspera & e.autosEnPuente = none
} for 9

// El puente siempre esta elevado o bajo, pero no en ambos.
// El iff se hace true si ambas son V o ambas son F (esto ultimo es: el puente no esta elevado,
// y sí esta bajo).
// No encuentra contraejemplos.
check puenteSiempreEnUnaSolaSituacion {
	all puente: Estado.puente | 
		(puente in Elevado iff puente not in Bajo)
} for 9

// Vemos si es posible que no haya barcos en un determinado momento.
// Encuentra instancias gracias al cambio en el multiplicador.
run sinBarcos {
	some e: Estado | no e.barcosEnEspera
} for 9

// Caso donde no hay un auto en el puente.
// Encuentra instancias gracias al cambio en el multiplicador.
run puenteVacio {
	some e: Estado | no e.autosEnPuente
} for 9

// Caso donde el puente esta elevado y hay un auto sobre el.
// No encuentra instancias como debe ser gracias al hecho.
run autosEnPuenteElevado {
	some e: Estado, a: Auto | a in e.autosEnPuente and e.puente in Elevado
} for 9

// Caso donde el puente esta elevado pero los barcos no cruzan.
// Encuentra instancias. Si bien esta validacion es mas de dinamica, es interesante comprobar
// que los barcos no cruzan por mas que el puente este elevado.
run barcoEnEsperaConPuenteElevado {
	some e: Estado | e.puente = Elevado and some e.barcosEnEspera
}

// Testeo de dinamica mas que de estatica.
run barcosCruzaConPuenteBajo {
	some e1: Estado - last, b: Barco | let e2 = e1.next |
		(e1+e2).puente = Bajo and
		(b in e1.barcosEnEspera) and
		(b not in e2.barcosEnEspera)
}

run llegaAutoAlPuente {
	some e: Estado - last, a: Auto | 
		a not in e.autosEnEspera and 
		a in e.next.autosEnEspera
}

/*
Agregar los predicados y/o facts necesarios para modelar la dinámica del problema. Considere
que los cambios de estados se producen porque:

- llega un barco al puente; o
- llega un auto al puente; o
- sube un auto al puente (el puente debe estar bajo); o
- baja un auto del puente (el auto de debe estar en el puente); o
- cruza un barco (el puente debe estar elevado y el barco debe estar esperando); o
- cambia la posición del puente (cambia de elevado a bajo o de bajo a elevado).

Estas acciones deben ser disjuntas, es decir los cambios de estados se producen por la 
ocurrencia de solo una de ellas. Escriba la especificación para que asi sea.
*/


// Inicialmente hay dos barcos en espera y dos autos en espera, con el puente en bajo.
// No hay restriccion sobre los autos en el puente al inicio.
fact init {
	#(first.barcosEnEspera) = 2 and
	#(first.autosEnEspera) = 2 and
	first.puente = Bajo
}

// Las transiciones entre estados se dan por las siguientes operaciones.
fact traces {
	all e1: Estado - last | let e2 = e1.next |
		llegaBarco[e1, e2] or
		llegaAuto[e1, e2] or
		subeAuto[e1, e2] or
		bajaAuto[e1, e2] or
		cruzaBarco[e1, e2] or
		cambiaPuente[e1, e2]
}

pred llegaBarco[e1, e2: Estado] {
	(some b: Barco |
		b not in e1.barcosEnEspera and
		e2.barcosEnEspera = e1.barcosEnEspera + b
	) and
	(e2.autosEnEspera = e1.autosEnEspera) and
	(e2.autosEnPuente = e1.autosEnPuente) and
	(e2.puente = e1.puente)
}

// Predicado que modela el comportamiento de la llegada de UN auto al puente (no sube).
pred llegaAuto[e1, e2: Estado] {
	(some a: Auto | 
		a not in e1.autosEnEspera and
		e2.autosEnEspera = e1.autosEnEspera + a
	) and
	(e2.barcosEnEspera = e1.barcosEnEspera) and
	(e2.autosEnPuente = e1.autosEnPuente) and
	(e2.puente = e1.puente)
}

// Predicado que modela el comportamiento de que un auto se suba al puente.
pred subeAuto[e1, e2: Estado] {
	(some a: e1.autosEnEspera |
		-- redundante, "a" es de los autos en espera.
--		(a not in e1.autosEnPuente) and
		(e1.puente = Bajo) and
		(e2.autosEnPuente = e1.autosEnPuente + a) and
		(e2.autosEnEspera = e1.autosEnEspera - a)
	) and
	(e2.puente = e1.puente) and
	(e2.barcosEnEspera = e1.barcosEnEspera)
}

// Predicado que modela el comportamiento de que un auto se baje del puente.
pred bajaAuto[e1, e2: Estado] {
	(some a: e1.autosEnPuente |
//		redundante porque si el puente tiene autos entonces esta bajo
//		(e1.puente = Bajo) and
		(e2.autosEnPuente = e1.autosEnPuente - a)
	) and
	(e2.autosEnEspera = e1.autosEnEspera)
	(e2.puente = e1.puente) and
	(e2.barcosEnEspera = e1.barcosEnEspera)
}

// Predicado que modela el comportamiento de que un barco en espera cruce el puente.
pred cruzaBarco[e1, e2: Estado] {
	(some b: e1.barcosEnEspera |
		(e1.puente = Elevado) and
		(e2.barcosEnEspera = e1.barcosEnEspera - b)
	) and
	(e2.puente = e1.puente) and
	(e2.autosEnEspera = e1.autosEnEspera) and
	(e2.autosEnPuente = e1.autosEnPuente)
}

// Predicado que modela el comportamiento de subir o bajar el puente.
pred cambiaPuente[e1, e2: Estado] {
	(no e1.autosEnPuente) and
	(e1.puente = Bajo implies e2.puente = Elevado) and
	(e1.puente = Elevado implies e2.puente = Bajo) and
	(e2.barcosEnEspera = e1.barcosEnEspera) and
	(e2.autosEnEspera = e1.autosEnEspera)
}


----------------------- Validacion dinamica -------------------------

run llegaBarcoCasoExito1 {
	some e: Estado - last | llegaBarco[e, e.next]
} for 5

run llegaAutoCasoExito1 {
	some e: Estado - last | llegaAuto[e, e.next]
} for 5

run cambiaPuenteCasoExito1 {
	some e: Estado - last | cambiaPuente[e, e.next]
} for 5

run bajaAutoDelPuenteCasoExito1 {
	some e: Estado - last | bajaAuto[e, e.next]
} for 5

// Buscamos que se satisfagan ambas operaciones en un par de estados.
// No encuentra instancias, lo que indica que no es posible satisfacer ambos a la vez y es una
// buena senial porque se busca que solo una de las operaciones ocurra por cambio de estado
run llegaAutoYCambiaElPuente {
	some e: Estado - last | llegaAuto[e, e.next] and cambiaPuente[e, e.next]
} for 5

run llegaAutoYCruzaBarco {
	some e: Estado - last | llegaAuto[e, e.next] and cruzaBarco[e, e.next]
} for 5

run cambiaPuenteYCruzaBarco {
	some e: Estado - last | cambiaPuente[e, e.next] and cruzaBarco[e, e.next]
} for 9

run subeAutoCasoExito1 {
	some e: Estado - last | subeAuto[e, e.next]
} for 5

// Verificamos que siempre que un auto se baje del puente, no volvera a aparecer.
// Encuentra un contraejemplo correcto: puede ocurrir que un auto suba al puente, lo cruce,
// baje del puente y al ratito vuelva a querer subir.
check autoQueBajaDelPuenteDesapareceParaSiempre {
	all e1: Estado - last, a: Auto | let e2 = e1.next | 
		(a in e1.autosEnPuente) implies (a not in (e2+nexts[e2]).autosEnEspera)
} for 9

check autoQueBajaDelPuenteDesapareceInmediato {
	all e1: Estado - last, a: Auto | let e2 = e1.next | 
		(a in e1.autosEnPuente) implies (a not in e2.autosEnEspera)
} for 9

run cruzaBarcoCasoExito1 {
	some e: Estado - last | cruzaBarco[e, e.next]
} for 5

// Caso donde sucede simultaneamente que baje el puente y suba un auto a el
run bajaPuenteSubeAuto {
	some e: Estado - last | 
		cambiaPuente[e, e.next] and 
		some (e.next).autosEnPuente
} for 9

// Caso donde un auto se queda en el puente por dos estados seguidos
run autoEnPuentePorDosEstadosConsecutivos {
	some e1: Estado - last | let e2 = e1.next | 
		(some e1.autosEnPuente and some e2.autosEnPuente)
} for 5

run subeAutoLlegaAuto {
	some e1: Estado - last | let e2 = e1.next | let e3 = e2.next |
		(#nexts[e1] >= 2) and
		subeAuto[e1, e2] and
		llegaAuto[e2, e3]
} for 9

run muchosAutosEnPuente {
	some e: Estado | #e.autosEnPuente > 1
} for 5

// No encuentra instancias. Por que? Es porque siempre que sube uno, debe bajar 
// inmediatamente y eso no le da tiempo a otros autos a subir?
check enTodoMomentoHaySoloUnAutoEnPuente {
	all e: Estado | lone e.autosEnPuente 
} for 16


------------ (d) -------------

// Si hay un auto en el puente, puede mantenerse sobre el puente en forma indeterminada.
// No encuentra instancias. No es posible que ocurra.
// Por que no podria ser posible que el auto se quede sobre el puente, y las unicas 
// operaciones que ocurran fueran las de llegaAuto o llegaBarco?
run autoIndefinido1 {
	some e: Estado - last, a: Auto | 
		a in e.autosEnPuente and
		(all e_sigs: nexts[e] | a in e_sigs.autosEnPuente)
} for 16 

run autoIndefinido2 {
	some a: Auto | let e = next[next[first]] |
		a in e.autosEnPuente and llegaBarco[e, e.next]
 		--(all e_sigs: nexts[e] | a in e_sigs.autosEnPuente)
} for 16 

run autoIndefinido3 {
	some e: Estado - last, a: Auto |
		(a in e.autosEnPuente) and
		(no e1: nexts[e] - last | let e2 = e1.next | 
			e1.puente = Bajo and e2.puente = Elevado
		)
} for 9

run subeAutoYSoloLleganAutosOBarcos {
	some e: Estado - last, a: Auto |
		// el auto esta en el puente...
		a in e.autosEnPuente and
		// ... y hay estados siguientes...
		#(nexts[e] - last) >= 2 and
		// ... y el auto no bajo del puente en el estado inmediato siguiente
		not bajaAuto[e, e.next] and
		// el resto de los estados siguientes son tales que solo se efectuaron las
		// operaciones de llegaAuto o de llegaBarco
		(all e1: nexts[e] - last | let e2 = e1.next | 
			llegaAuto[e1, e2] or llegaBarco[e1, e2]
		)
} for 9



------- (e) --------

// El puente siempre estará bajo en el estado inmediato siguiente de aquel en el cual hay
// algún auto sobre el puente.
// No encuentra contraejemplos. La propiedad se cumple.
check propiedad1 {
	all e1: Estado - last | let e2 = e1.next |
		(some e1.autosEnPuente) implies (e2.puente = Bajo)
} for 9

// En todos los estados, si hay un auto en el puente entonces en el próximo estado ya no lo
// está.
// No encuentra contraejemplos. La propiedad se cumple.
check propiedad2 {
	all e1: Estado - last | let e2 = e1.next |
		(some e1.autosEnPuente) implies (no e2.autosEnPuente)
} for 9

------ (f) --------

/*
Si se garantiza la prioridad del descenso del auto que esta en el puente por sobre las otras
operaciones, la respuesta a la propiedad 2 sigue siendo que se cumple.


*/
