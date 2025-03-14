open util/ordering [Tiempo] as ord

one sig Semaforo {
	// ahora vamos a tener tuplas Color-Tiempo. 
	// Para cada Tiempo hay un solo Color.
	// Un Color puede aparecer en multiples Tiempos.
	situacion: Color one -> Tiempo
}

abstract sig Color {}

// queremos que un semaforo tenga un sólo color en un determinado momento.
one sig Rojo, Amarillo, Verde extends Color {}

sig Tiempo {}

// Funcion que permita establecer la secuencia de colores
// apropiada para el semáforo.
// ¿Cuáles son las tuplas válidas en mi semáforo?
fun secuenciaColor: Color -> Color {
	(Rojo->Verde)+(Verde->Amarillo)+(Amarillo->Rojo)+(Color<:iden)
}

// cómo cambio de estado? Cuando el semáforo cambia de color
// necesito parametrizar el semáforo si estamos en una situación donde hay muchos semáforos.
pred cambioLuz [t1, t2: Tiempo, s: Semaforo] {
	some c1, c2: Color | 
		(c1->c2) in secuenciaColor and
		// el color en el timestamp 1 y en el timestamp 2 son válidos 
		(c1->t1) in s.situacion and 
		(c2->t2) in s.situacion
}

// relación entre los estados locales: cual es la posibilidad entre los cambios de estado
fact traces {
	all s: Semaforo | 
		//el unico semaforo que tenemos empieza en color rojo
		// el primer timestamp y el semaforo validan el predicado init
		init[ord/first, s] and
		all s: Semaforo, t: Tiempo-ord/last | let t1=t.next | cambioLuz[t, t1, s]
}

// la situacion de comienzo del semaforo
pred init [t: Tiempo, s: Semaforo] {
	Rojo->t in s.situacion
}

-------------------------------

pred buscar {some s: Semaforo, t: Tiempo | Amarillo->t in s.situacion}
run buscar for 1 Semaforo, 9 Tiempo

pred buscar2 {some s: Semaforo | Amarillo ->ord/last in s.situacion}
run buscar2 for 1 Semaforo, 8 Tiempo

run {}
