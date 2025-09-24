/*
Situacion:
Tenemos un semaforo que va cambiando de color. Queremos modelar la dinamica de que
el semaforo vaya cambiando de color.
En este archivo, lo hacemos con la estrategia de estados locales, o lo que es lo mismo, 
estampillas de tiempo; es decir, las signaturas mantienen toda la dinamica de la situacion,
y tienen una estampilla de tiempo al final (ultima columna) para mostrar la evolucion.
*/

open util/ordering [Tiempo]

one sig Semaforo {
	// cada Color esta vinculado a cero, uno o varios Tiempos.
	// cada Tiempo viene vinculado desde solo un Color.
	// Esto es, en cada tiempo hay un color en el semaforo, que puede repetirse en otro tiempo
	// Dado que hay un solo semaforo, podria definirse la relacion situacion: set Tiempo en la
	// signatura de Color.
	situacion: Color one -> Tiempo
}

abstract sig Color {}

// queremos que un semaforo tenga un sólo color en un determinado momento.
one sig Rojo, Amarillo, Verde extends Color {}

sig Tiempo {}

// Volvemos a definir la secuencia correcta de colores.
fun secuenciaValidaDeColores: set Color->Color {
	(Verde->Amarillo) + (Amarillo->Rojo) + (Rojo->Verde) + (Color <: iden)
}

pred cambiarLuz [t1, t2: Tiempo] {
	Semaforo.situacion.t1 -> Semaforo.situacion.t2 in secuenciaValidaDeColores
}

fact init {
	// inicialmente el semaforo esta rojo
	Semaforo.situacion.first = Rojo
}

fact traces {
	// la forma en que transicionan los tiempos es con el predicado cambiarLuz
	all t: Tiempo - last | cambiarLuz[t, t.next]
}

run default {} for 8 Tiempo

