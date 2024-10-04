open util/ordering[State] as ord

sig Semaforo{ situacion:  set State}
// me concentro en un solo semáforo.
// si quisiera más semáforos: 
sig State { situacion: Semaforo -> one Color }
//sig State { luz: one Color}
abstract sig Color {}
one sig Rojo, Amarillo, Verde extends Color {}

-- el cambio de colores debe seguir una secuencia apropiada
fun secuenciaColor: Color -> Color {
     (Color <: iden) + (Rojo-> Verde) + (Verde-> Amarillo) + (Amarillo -> Rojo)
 }

-- el semaforo soli puede cambiar su luz
pred cambioLuz(s,s1: State, sem: Semaforo) {
	sem.(s.situacion) -> sem.(s1.situacion) in secuenciaColor
}


-- relacion entre los estados
fact traces{ 
	all sem: Semaforo |
		init [ord/first, sem] and
			all s:State - ord/last | let s1= s.next | cambioLuz[s,s1, sem]
}

-- el semáforo comienza en color Rojo
pred init[s:State, sem: Semaforo] { 
	sem.(s.situacion) = Rojo
}

pred buscar {
	some sem: Semaforo | sem.(ord/last.situacion) = Amarillo
} 

run buscar for 8 State, 1 Semaforo
