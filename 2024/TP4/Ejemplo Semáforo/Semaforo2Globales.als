open util/ordering [Estado] as ord

one sig Semaforo {}

abstract sig Color {}
one sig Rojo, Amarillo, Verde extends Color {}

// el estado es un conjunto de situaciones donde:
// para cada semáforo, tenemos un solo color.
// este modelo es útil cuando tenemos varios semáforos
sig Estado {
	situacion: Semaforo -> one Color
}

fun secuenciaColor: Color -> Color {
	(Rojo->Verde)+(Verde->Amarillo)+(Amarillo->Rojo)+(Color<:iden)
}

pred cambioLuz [e1, e2: Estado, s: Semaforo] {
	// la luz en el estado1 y la luz en el estado2 sean válidos
	(s.(e1.situacion) -> s.(e2.situacion)) in secuenciaColor
}

// cómo paso de un estado al siguiente? mediante cambioLuz
fact traces {
	all s: Semaforo | 
		init[ord/first, s] and
		all e: Estado-ord/last | cambioLuz[e, e.next, s]
}

pred init [e: Estado, s: Semaforo] {
	// como solo hay un semáforo, podemos setearlo en rojo
	s.(e.situacion) = Rojo
}

pred buscar {
	some s: Semaforo | s.(ord/last.situacion) = Amarillo
}

run buscar for 8 Estado, 1 Semaforo

pred buscar2 {
	some s: Semaforo, e: Estado |
		s.(e.situacion) = Amarillo
}

run buscar2 for 6 Estado, 1 Semaforo
