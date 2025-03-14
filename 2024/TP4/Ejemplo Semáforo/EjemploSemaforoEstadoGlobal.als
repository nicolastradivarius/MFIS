// en este enfoque, el Estado es el que retiene o encapsula el comportamiento que queremos 
// mantener de la dinámica como primer elemento de la tupla

open util/ordering[Estado] as ord

one sig Semaforo {
	// la situacion va a ser un conjunto de estados
	// no tenemos una relacion ternaria porque sólo tenemos un semaforo.
	// si hubiera más semáforos, necesitariamos una relacion ternaria del tipo
	// situacion: Estado set -> one Color
	// en ese caso, cada Semáforo tiene un conjunto de estados
	// y cada Estado tiene un sólo color. Uno podría pensar que esto imposibilita la situación en que
	// un semáforo esté en Verde en un determinado estado, y otro semáforo esté en Rojo en ese
	// mismo estado. Sin embargo, las restricciones de multiplicidad aplican de manera individual
	// sobre los átomos de semáforo, entonces, (s1, e1, Verde) y (s2, e1, Rojo) no son tuplas
	// conflictivas. Sí lo serían (s1, e1, Verde) y (s1, e1, Rojo)
	situacion: set Estado
}

abstract sig Color {}

one sig Rojo, Amarillo, Verde extends Color {}

// el Estado dice cuáles son las luces por las que va pasando un semaforo en particular
sig Estado {
	// el único semáforo, en un determinado estado, solo tiene un color
	luz: one Color
}

// la secuencia de colores es la misma
fun secuenciaColor: set Color -> Color {
	// con Color<:iden nos quedamos con las tuplas de iden que empiezan con átomos de Color
	// es decir, nos quedamos con (Rojo, Rojo), etc.
	(Rojo->Verde) + (Verde->Amarillo) + (Amarillo->Rojo) + (Color <: iden)
}

// ahora volvemos a cubrir los requerimientos de antes: indicar como haremos los cambios de estado,
// la relacion entre los estados para poder tener el comportamiento de la maquina virtual

// en este caso, no indicaremos el semáforo, ya está identificado explicitamente con la relacion
// de situacion que involucran los estados, y solo hay un semaforo.
pred cambioLuz [e1, e2: Estado] {
	// el cambio de luz es posible cuando pasamos de la luz del estado 1 a la luz del estado 2
	// respetando la secuencia valida de colores.
	(e1.luz -> e2.luz) in secuenciaColor
}

fact traces {
	// el semáforo empieza en Rojo
	init[ord/first] and
	// para todos los estados excepto el último, el vínculo entre el estado y el siguiente es a traves
	// del cambio de luz. Es decir, se pasa de e1 a e2 con un cambio de Rojo a Verde, etc.
	(all e: Estado-ord/last | cambioLuz[e, e.next])
}

pred init [e: Estado] {
	e.luz = Rojo
}


// queremos ver que el último estado sea talq ue el semáforo esta amarillo.
pred buscar {
	ord/last.luz = Amarillo
}

pred buscarAlgunEstadoAmarillo {
	some e: Estado | e.luz = Amarillo
}

run buscar for 9 Estado, 1 Semaforo

run buscarAlgunEstadoAmarillo for 8 Estado, 1 Semaforo
