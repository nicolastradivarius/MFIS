/*
Enunciado:
Un granjero tiene que cruzar un rio con 3 objetos: un Zorro, una Gallina y Grano.
Solo puede cruzar el rio con un objeto a bordo de un bote (ademas del Granjero mismo).
Por lo tanto, debe dejar dos objetos en la orilla de partida.
El problema es que hay ciertas combinaciones de objetos que, al dejarlos solos, sucede que
uno de ellos desaparece. Esas combinaciones son las siguientes:
- Si se quedan el Zorro y la Gallina, desaparece la gallina porque el zorro se la comio.
- Si se quedan la Gallina y el Grano, desaparece el grano porque la gallina se lo comio.
La unica combinacion que no da problemas es que se queden el Zorro con el Grano.
*/

// La signatura Estado esta ordenada. Hay un primer y ultimo atomo, y un orden establecido
// entre los atomos del medio.
open util/ordering[Estado]


abstract sig Objeto {
	// cada objeto puede comer o no a otro objeto.
	come: lone Objeto
}
// la relacion "come" esta en una signatura que no esta ordenada.
// esta relacion se llama "estatica" porque permanece invariante a lo largo del tiempo (estados).

one sig Granjero, Zorro, Gallina, Grano extends Objeto {}

fact "quien come a quien" {
	// definimos la relacion como la union de las siguientes tuplas:
	come = (Zorro->Gallina) + (Gallina->Grano)
	// esta relacion va a ser asi durante toda la evolucion.
}

sig Estado {
	// cada estado se vincula con un conjunto de objetos presentes en las dos orillas que hay.
	orillaIzquierda, orillaDerecha: set Objeto
}

fact init {
	// inicialmente todos los objetos estan del lado izquierdo.
	// el estado "first" es el primero de todos.
	first.orillaIzquierda = Objeto and
	no first.orillaDerecha
}

// hecho que determina que todo estado debe cumplir estas condiciones para ser valido:
// un objeto no puede estar en ambas orillas en el mismo estado; y
// las dos orillas contienen todos los objetos del problema.
fact esValido {
	all e: Estado | 
		e.orillaIzquierda & e.orillaDerecha = none and
		e.orillaIzquierda + e.orillaDerecha = Objeto
}

// operaciones para pasar de un estado al siguiente:
// ep = estado de partida, el = estado de llegada
pred cruzarRio[ep, el: Estado] {
	// como solo el granjero puede cruzar de una orilla a la otra, entonces la unica orilla
	// desde donde puedo cruzar es aquella donde este el granjero.
	(Granjero in ep.orillaIzquierda implies CruzarIzquierdaDerecha[ep, el]) and
	(Granjero in ep.orillaDerecha implies CruzarDerechaIzquierda[ep, el])
}

// modela el comportamiento de cruzar de la orilla izquierda a la orilla derecha.
pred CruzarIzquierdaDerecha[ep, el: Estado] {
	// el granjero cruza el rio, o bien solo, o bien con un (y solo un) objeto.
	// selecciono uno de los objetos de la orilla izquierda. Entre esos objetos, tengo en cuenta
	// al granjero, porque si Alloy lo elige a el, entonces viaja solo. En otro caso, Alloy elige
	// al objeto con el cual viajara el Granjero (o sea, en cualquier caso, el granjero viaja).
	some item: ep.orillaIzquierda |
		// despues de cruzar, la orilla izquierda queda sin el granjero, sin el item elegido, y
		// tambien sin el objeto que pudiera ser comido. Por ejemplo, si el objeto elegido es
		// el zorro, y en la orilla izquierda quedan la gallina y el grano, entonces 
		// (el.orillaIzquierda).come = Grano porque en "come" esta la tupla (Gallina->Grano) y
		// la gallina que queda hace match. Al quitar el objeto Grano de la orilla izquierda,
		// se fuerza a que el estado quede inconsistente, porque ahora la orilla izquierda
		// ya no contiene a todos los objetos del problema. Asi, evito que me queden objetos 
		// que se coman entre sí en una orilla.
		el.orillaIzquierda = ep.orillaIzquierda - Granjero - item - (el.orillaIzquierda).come and
		// despues de cruzar, la orilla derecha contiene al granjero y al item elegido
		el.orillaDerecha = ep.orillaDerecha + Granjero + item
}

// modela el comportamiento de cruzar de la orilla derecha a la orilla izquierda.
pred CruzarDerechaIzquierda[ep, el: Estado] {
	some item: ep.orillaDerecha |
		el.orillaDerecha = ep.orillaDerecha - Granjero - item - (el.orillaDerecha).come and
		el.orillaIzquierda = ep.orillaIzquierda + Granjero + item
}

// determino como va a ser el cambio de un estado al siguiente.
fact traces {
	all e: Estado - last |
		cruzarRio[e, e.next]
}

// Busca un estado donde todos los objetos hayan cruzado de la orilla izq a la derecha.
run cruzaronTodos {
	some e: Estado | Objeto in e.orillaDerecha
} for 9 Estado

// Busca un estado donde el zorro haya cruzado de la orilla izq a la derecha
run zorroCruzo {
	some e: Estado | Zorro in e.orillaDerecha
} for 9 Estado

// Busca una situacion en la que la gallina este del lado izquierdo en el ultimo estado.
// Como el scope por defecto es 3, si no se especifica, sera el estado$2 el que lo cumpla.
run gallinaUltimoEstado {
	Gallina in last.orillaIzquierda
}

// Busca algun estado que no sea valido. Ej, la gallina y el grano esten en una misma orilla sin
// el granjero presente.
run estadoNoValido {
	some e: Estado | 
		((Gallina+Grano) in (e.orillaIzquierda) and Granjero not in e.orillaIzquierda) or
		((Gallina+Grano) in (e.orillaDerecha) and Granjero not in e.orillaDerecha)
} for 18 Estado
