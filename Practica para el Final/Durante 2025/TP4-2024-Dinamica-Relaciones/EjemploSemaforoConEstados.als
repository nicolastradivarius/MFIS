/*
Situacion:
Tenemos un semaforo que va cambiando de color. Queremos modelar la dinamica de que
el semaforo vaya cambiando de color.
En este archivo, lo hacemos con la estrategia de estados globales; es decir, los estados engloban
toda la dinamica de la situacion, estando primero en las relaciones.
*/

open util/ordering [Estado] as ord

one sig Semaforo {}

abstract sig Color {}
one sig Rojo, Amarillo, Verde extends Color {}

// Definimos el estado como un conjunto de situaciones en las que, para cada una,
// el unico semaforo que existe tiene un color especifico.
sig Estado {
	// cada Semaforo es mapeado a exactamente un Color.
	// cada Color viene mapeado de cero, uno o muchos Semaforos (keyword set por defecto).
	// Como solo hay un semaforo, se puede directamente mapear estados a colores.
	situacion: one Color
	// situacion: Semaforo -> one Color
}

// Definimos una funcion que devuelva el conjunto de transiciones posibles para el semaforo.
fun secuenciaValidaDeColores: set Color->Color {
	(Verde->Amarillo) + (Amarillo->Rojo) + (Rojo->Verde) + (Color <: iden)
	// (Color <: iden) lo que hace es una restriccion de dominio a la relacion "iden" tomando
	// los atomos de Color como filtro. En otras palabras, se queda con las tuplas de "iden" que
	// comiencen con atomos de Color, y como iden contiene de tuplas a todos los atomos
	// del universo relacionados con si mismos, esto resulta en (Rojo->Rojo), (Verde->Verde), etc.
}

// Predicado que define una transicion de color del semaforo.
// Una transicion es valida cuando la situacion de los estados forma parte de la secuencia valida.
pred cambiarLuz [e1, e2: Estado] {
	//(e1.situacion -> e2.situacion) in secuenciaValidaDeColores
	((e1.situacion in Rojo) implies (e2.situacion in Rojo+Verde)) and
	((e1.situacion in Verde) implies (e2.situacion in Verde+Amarillo)) and
	((e1.situacion in Amarillo) implies (e2.situacion in Amarillo+Rojo))
}

/*
Otra manera posible es la siguiente:

((e1.situacion in Rojo) implies (e2.situacion in Rojo+Verde)) and
((e1.situacion in Verde) implies (e2.situacion in Verde+Amarillo)) and
((e1.situacion in Amarillo) implies (e2.situacion in Amarillo+Rojo))
*/

run default {} for 7 Estado

fact init {
	// Inicialmente el semaforo esta en Rojo
	(first.situacion in Rojo)
}

fact traces {
	// Los cambios entre estados se dan por el predicado cambiarLuz
	all e: Estado - last | cambiarLuz[e, e.next]
}

// Buscamos que el ultimo estado sea tal que el semaforo esta en amarillo
run buscarAmarillo {
	last.situacion = Amarillo
} for 9 Estado
