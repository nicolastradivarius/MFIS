/*
Considere un puente levadizo sobre el que pasan autos cuando se encuentra bajo, permitiendo
también el paso de barcos (por debajo de él) cuando esta elevado. Considere que en toda
instancia deben existir al menos dos barcos y al menos dos autos. Por seguridad, en
todo momento puede haber como máximo un auto sobre el puente.
*/

open util/ordering[Estado] as ord

sig Barco { }

sig Auto { }

abstract sig EstadoPuente { }

one sig Elevado, Bajo extends EstadoPuente { }

sig Estado {
	puente: one EstadoPuente,
	barcosEnEspera: some Barco,
	autosEnEspera: set Auto,
	autosEnPuente: one Auto
}

run default {}

// chequeamos que no haya un auto esperando y en el puente al mismo tiempo.
// Encuentra contraejemplos en los que un mismo auto esta en el puente y fuera de el.
check autoEsperandoYEnPuente {
	all e: Estado| e.autosEnEspera & e.autosEnPuente = none
}

// El puente siempre esta elevado o bajo, pero no en ambos.
// El iff se hace true si ambas son V o ambas son F (esto ultimo es: el puente no esta elevado,
// y sí esta bajo).
// No encuentra contraejemplos.
check puenteSiempreEnUnaSolaSituacion {
	all puente: Estado.puente | 
		(puente in Elevado iff puente not in Bajo)
} for 9

// Vemos si es posible que no haya barcos en un determinado momento.
// No encuentra instancias, lo cual esta mal porque esto deberia ser posible, ya que realmente
// no hay barcos todo el tiempo queriendo cruzar.
run sinBarcos {
	some e: Estado | no e.barcosEnEspera
} for 9

// Caso donde no hay un auto en el puente.
// No encuentra instancias, lo cual esta mal, porque en algun momento el puente debe quedar
// libre.
run puenteVacio {
	some e: Estado | no e.autosEnPuente
} for 9

// Caso donde el puente esta elevado y hay un auto sobre el.
// Existe un auto sobre el puente cuando esta elevado. No deberia ocurrir, ya que el auto
// quedaria "en el aire". A menos que se considere que el auto esta con el freno de mano 
// y en pendiente, elevandose a la par que el puente mientras espera, la situacion que se 
// considera correcta aqui es que para que el puente elevar no debe haber autos encima de el;
// de esta forma nunca quedaria un auto encima del puente mientras esta elevado.
run autosEnPuenteElevado {
	some e: Estado, a: Auto | a in e.autosEnPuente and e.puente in Elevado
}

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
