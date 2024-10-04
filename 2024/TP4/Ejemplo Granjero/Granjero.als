/*
Problema: lograr que el granjero viaje con todos sus objetos sin que uno desaparezca.

*/

open util/ordering[Estado]

// relaciones estáticas: se van a mantener igual durante toda la evolución del tiempo.
// son aquellas presentes en signaturas que no están ordenadas.
abstract sig Objeto {
	come: set Objeto
}

one sig Granjero, Zorro, Gallina, Grano extends Objeto {}

fact {
	come = Zorro->Gallina + Gallina->Grano
}

sig Estado {
	orillaDerecha, orillaIzquierda: set Objeto
}

fact {
	// los objetos empiezan todos juntos en la orilla derecha.
	first.orillaDerecha = Objeto && no first.orillaIzquierda
}

// ¿Cuándo un estado es válido? ¿Qué restricciones tiene que satisfacer?
// Que un objeto no esté en ambas orillas al mismo tiempo, que en todo estado
// las dos orillas contengan todos los objetos existentes
pred esValido[e: Estado] {
	e.orillaDerecha + e.orillaIzquierda = Objeto and
	(e.orillaDerecha & e.orillaIzquierda = none)
}

// me aseguro que todos los estados son válidos
fact {
	all e: Estado | esValido[e]
}

// definamos las operaciones que me permiten cambiar de estado

// ep = estado de partida
// el = estado de llegada
pred cruzarRio[ep, el: Estado] {
	// solo el granjero puede cruzar. esto significa que debo cruzar desde la orilla donde está el granjero.
	// si el granjero está en la orilla izquierda, los cambios van a ser de izquierda a derecha.
	(Granjero in ep.orillaIzquierda implies CruzarIzquierdaDerecha[ep, el]) and
	(Granjero in ep.orillaDerecha implies CruzarDerechaIzquierda[ep, el])
}

pred CruzarIzquierdaDerecha[e1, e2: Estado] {
	// el granjero está en la orilla izquierda.
	// ¿cuál es el efecto de la operación? ¿Quién cruza el río? El granjero con una sola cosa.
	// elijo un objeto entre todos los objetos de la orilla izquierda (incluyendo al granjero, para permitirle que cruce solo, sin objetos)
	// si lo quito de la cuantificación, debería hacer otro predicado que modele el cruce del Granjero solo.

	some item: e1.orillaIzquierda | 
		e2.orillaIzquierda = e1.orillaIzquierda - Granjero - item - (e2.orillaIzquierda).come and
		e2.orillaDerecha = e1.orillaDerecha + Granjero + item
		// al quitarle e2.orillaIzquierda.come logro que con el paso de los estados, los objetos que deban comerse entre sí 
		// efectivamente lo hagan. Además, evito que me queden objetos que se coman entre sí en una orilla, porque los quito
		// y de otro modo el estado dejaría de ser válido. 
		// Esto resulta vacío si cruzo el objeto correcto (tal que los que me queden no se coman).
}

pred CruzarDerechaIzquierda[e1, e2: Estado] {
	// puedo restringir acá que el granjero tiene que estar en la orilla derecha. Si lo hago, puedo utilizar estos predicados en el
	// traces. Caso contrario, debo utilizar el predicado cruzarRio ya que ahí se chequea que el granjero esté en su respectiva orilla.
	some item: e1.orillaDerecha |
		e2.orillaDerecha = e1.orillaDerecha - Granjero - item - (e2.orillaDerecha).come and
		e2.orillaIzquierda = e1.orillaIzquierda + Granjero + item
} 

// ¿Cómo paso de un estado al siguiente?
fact traces {
	all e: Estado - last | 
		CruzarIzquierdaDerecha[e, e.next] or CruzarDerechaIzquierda[e, e.next]
		// otra forma simple es poner let ef = e.next para que no quede "e.next" por todos lados
}

// comando para mover elementos
run zorroCruzo {
	some e: Estado | Zorro in e.orillaIzquierda
}

run gallinaUltimoEstado {
	Gallina in last.orillaIzquierda
}

run cruzaronTodos {
	// tener cuidado con pedir que las cosas pasen en el ultimo estado.
	Objeto in last.orillaIzquierda
} for 10 Estado

// la manera correcta de resolverlo es ver si es posible encontrar un estado donde suceda
run cruzaronTodos2 {
	some e: Estado | Objeto in e.orillaIzquierda
} for 9 Estado

// Podría armar un predicado no_valido donde ponga que en la orilla izquierda esté Gallina->Grano o Zorro->Gallina
// y lo mismo para la otra orilla,

// La mayoría de las propiedades siguen el patrón de "para todo estado, si cierto objeto está en el estado, entonces avanzo"

// En el problema de los Misioneros & Canibales necesito agregar el bote en el modelo para saber de qué orilla a qué orilla puedo cruzar
