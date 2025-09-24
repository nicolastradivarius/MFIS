/*
Problema de los misioneros y canibales. Involucra a N misioneros y N canibales que deben 
cruzar un rio utilizando un bote que solo puede trasladar a **dos** personas a la vez.
El numero de canibales que se encuentran en cada orilla del rio en ningun momento puede
superar al numero de misioneros en la misma orilla.
El bote no puede cruzar el rio por si mismo, es decir, sin personas en el.

(a) Definir un modelo. Debe tener en cuenta en que orilla se encuentra cada persona. El cruce
de personas de una orilla a la otra es inmediato (no involucra estados intermedios con el bote
cruzando el rio).
*/

open util/ordering[Estado]

abstract sig Objeto {}

one sig Bote extends Objeto {}

some sig Misionero, Canibal extends Objeto {}

sig Estado {
	orillaIzquierda, orillaDerecha: set Objeto
}

fact cantidadDePersonas {
	// la cantidad de misioneros equivale a la de canibales
	#Misionero = #Canibal
}

fact {
	#Misionero = 3
}

fact init {
	(no first.orillaDerecha) and
	(first.orillaIzquierda = Objeto)
}

// Un estado es valido si:
// 	- todos los objetos estan repartidos entre las dos orillas
//	- no hay un mismo objeto en ambas orillas a la vez
// 	- la cantidad de canibales no supera a la de misioneros, o bien alguna de las dos orillas
// 	esta compuesta unicamente por canibales (no hay misioneros). Es necesario modelarlo
//	aparte ya que la restriccion de cardinalidad no tiene en cuenta este detalle.
pred esValido[e: Estado] {
	((e.orillaIzquierda + e.orillaDerecha) = Objeto) and
	(canibalesNoSuperaMisioneros[e] or noHayMisioneros[e]) and
	(e.orillaIzquierda & e.orillaDerecha = none)
}

// Determina si la cantidad de canibales no supera a la de misioneros.
pred canibalesNoSuperaMisioneros[e: Estado] {
	(#(e.orillaIzquierda & Canibal) <= #(e.orillaIzquierda & Misionero)) and
	(#(e.orillaDerecha & Canibal) <= #(e.orillaDerecha & Misionero))
}

// Determina si no hay misioneros en alguna de las dos orillas
pred noHayMisioneros[e: Estado] {
	(e.orillaIzquierda & Misionero = none) or
	(e.orillaDerecha & Misionero = none)
}

fact "todos los estados deben ser validos" {
	all e: Estado | esValido[e]
}

// dependiendo de la orilla donde este el bote, es el viaje que puede realizar
pred cruzarRio[e1, e2: Estado] {
	(Bote in e1.orillaIzquierda implies CruzarIzquierdaDerecha[e1, e2]) and
	(Bote in e1.orillaDerecha implies CruzarDerechaIzquierda[e1, e2])
}

pred CruzarIzquierdaDerecha[e1, e2: Estado] {
	// no exijo que sean disjuntos para permitir que viaje solo una persona (max. 2)
	some persona1, persona2: e1.orillaIzquierda - Bote |
		(e2.orillaIzquierda = e1.orillaIzquierda - persona1 - persona2 - Bote) and
		(e2.orillaDerecha = e1.orillaDerecha + persona1 + persona2 + Bote)
}

pred CruzarDerechaIzquierda[e1, e2: Estado] {
	some persona1, persona2: e1.orillaDerecha - Bote |
		(e2.orillaDerecha = e1.orillaDerecha - persona1 - persona2 - Bote) and
		(e2.orillaIzquierda = e1.orillaIzquierda + persona1 + persona2 + Bote)
}

fact traces {
	all e: Estado - last | cruzarRio[e, e.next]
}

run default {} for exactly 3 Misionero, exactly 3 Canibal, 32 Estado

run todosllegaron {
	some e: Estado | e.orillaDerecha = Objeto
} for 19

run misionerosDelLadoDerecho {
	some e: Estado | e.orillaDerecha = Misionero
} for 15
