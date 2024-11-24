/**
El problema Misioneros y Caníbales es un problema lógico clásico. Involucra a N misioneros y N 
caníbales que deben cruzar un río utilizando un bote que solo puede trasladar a dos personas a 
la vez. El número de caníbales que se encuentran en cada orilla del río en ningún momento puede
superar al número de misioneros en la misma orilla.
El bote no puede cruzar el río por sí mismo, es decir, sin personas en él.
*/


/**
(a) Definir un modelo, estableciendo los hechos y/o predicados que sean necesarios para modelar el 
problema. El modelo debe tener en cuenta en qué orilla se encuentra cada persona. Considere 
que el efecto del cruce de personas de una orilla a la otra utilizando el bote es inmediato (es 
decir, no deberán considerarse estados intermedios en los que hay personas arriba del bote que 
se están trasladando de una orilla a la otra).
*/

open util/ordering [Estado] as ord

abstract sig Objeto {}

abstract sig Persona extends Objeto {}

one sig Bote extends Objeto {}

sig Misionero, Canibal extends Persona {}

sig Estado {
	orillaIzquierda, orillaDerecha: set Objeto
}

// todos los objetos empiezan en la orilla izquierda.
fact init {
	Objeto in first.orillaIzquierda and
	no first.orillaDerecha 
}

// ¿Cuándo un estado es válido?
// 	- cuando no hay más canibales que misioneros en alguna de las dos orillas.
// 	- cuando el bote no está en ambas orillas al mismo tiempo.
// 	- cuando entre las dos orillas conforman todos los objetos existentes.
/*
Tengo que controlar:
	- si hay misioneros en una orilla, debo controlar la cardinalidad de los canibales <= misioneros
	- si no hay misioneros en una orilla, puede haber cualquier cantidad de canibales en ella
*/
pred esValido [e: Estado] {
	// ¿está bien planteado? ¿Estoy dejando afuera alguna condición?
	(some e.orillaIzquierda & Misionero implies (#(e.orillaIzquierda & Canibal) <= #(e.orillaIzquierda & Misionero))) and 
	(some e.orillaDerecha & Misionero implies (#(e.orillaDerecha & Canibal) <= #(e.orillaDerecha & Misionero))) and 
	(e.orillaIzquierda + e.orillaDerecha = Objeto) and
	(e.orillaIzquierda & e.orillaDerecha = none)
}

fact estados_validos {
	all e: Estado | esValido[e]
}

// ¿Cómo cambio de un estado al siguiente?
// Cuando paso dos o una personas de una orilla a la otra (mediante un bote).
fact traces {
	all e: Estado - ord/last | CruzarIzquierdaDerecha[e, e.next] or CruzarDerechaIzquierda[e, e.next]
}

pred CruzarIzquierdaDerecha [e1, e2: Estado] {
	Bote in e1.orillaIzquierda and
	some item1, item2: e1.orillaIzquierda-Bote | 
		e2.orillaIzquierda = e1.orillaIzquierda - Bote - item1 - item2 and
		e2.orillaDerecha = e1.orillaDerecha + Bote + item1 + item2
}

pred CruzarDerechaIzquierda [e1, e2: Estado] {
	Bote in e1.orillaDerecha and
	some item1, item2: e1.orillaDerecha-Bote | 
		e2.orillaDerecha = e1.orillaDerecha - Bote - item1 - item2 and
		e2.orillaIzquierda = e1.orillaIzquierda + Bote + item1 + item2
}


run cruzaronTodos {
	some e: Estado | Objeto in e.orillaDerecha
} for 12 Estado, exactly 3 Misionero, exactly 3 Canibal

// ¿De qué manera podría probar que mi modelo es correcto?
