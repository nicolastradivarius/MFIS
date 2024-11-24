open util/ordering[Tiempo] as ord

sig Semaforo {
	// la situación ya no es un solo color, sino que van a ser tuplas (Color, Tiempo)
	// para cada Tiempo hay un solo Color, pero para cada Color hay muchos Tiempos
	// lo que significa que un mismo color puede presentarse en multiples instantes de tiempo
	situacion: Color one -> set Tiempo
}

abstract sig Color {}

one sig Rojo, Amarillo, Verde extends Color {}

sig Tiempo {}

// definimos la funcion que permita establecer la secuencia de colores apropiada para el semaforo
fun secuenciaColor: set Color -> Color {
	// con Color<:iden nos quedamos con las tuplas de iden que empiezan con átomos de Color
	// es decir, nos quedamos con (Rojo, Rojo), etc.
	(Rojo->Verde) + (Verde->Amarillo) + (Amarillo->Rojo) + (Color <: iden)
}

// el semáforo cambia de color: el cambio de estado tiene lugar cuando cambia el color del semáforo
// le parametrizamos el semáforo porque tenemos varios, y necesitamos explicitar cuál va a cambiar.
// si tuvieramos un unico semáforo, no haría falta.
pred cambioLuz [t1, t2: Tiempo, sem: Semaforo] {
	some c1, c2: Color |
		(c1->c2) in secuenciaColor and
		// el color c1 es el que está presente en el tiempo 1
		(c1->t1) in sem.situacion and
		// el color c2 es el que está presente en el tiempo 2 (al que avanzamos)
		(c2->t2) in sem.situacion
}

// relación entre los tiempos: cuál es el ordenamiento o posibilidad entre los cambios de estado
fact traces {
	// la situacion inicial del semáforo es que está en Rojo. como tenemos uno, es factible
	(all sem: Semaforo | init[ord/first, sem]) and
	// los tiempos están relacionados por el cambio de luz del semaforo.
	// omitimos el ultimo estado porque no tiene un estado siguiente para vincularlo
	(all sem: Semaforo, t: Tiempo-ord/last | cambioLuz[t, t.next, sem])
}

// condición del primer estado/tiempo del semáforo: se encuentra con la luz en rojo.
// se expresa como que la tupla (Rojo, Tiempo) está en la situacion del semaforo
pred init [t: Tiempo, sem: Semaforo] {
	(Rojo->t in sem.situacion)
}

// hay algun semaforo y algun momento de tiempo en que el semáforo se ponga amarillo.
pred buscar {
	some s: Semaforo, t: Tiempo | (Amarillo->t) in s.situacion
}

// Recordar que indicar explicitamente el scope para Tiempo determina cuántos átomos va a tener
run buscar for 1 Semaforo, 9 Tiempo

// en vez de buscar por algún momento de tiempo, le pedimos que haya algun semaforo
// tal que termine siempre en color amarillo
pred buscar2 {
	some s: Semaforo | (Amarillo->ord/last) in s.situacion
}

run buscar2 for 1 Semaforo, 9 Tiempo

run default {}
