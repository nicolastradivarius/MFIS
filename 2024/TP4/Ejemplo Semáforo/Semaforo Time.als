open util/ordering[Time] as ord

sig Semaforo{ situacion:  set Color one -> Time}
abstract sig Color {}
one sig Rojo, Amarillo, Verde extends Color {}

sig Time{}

-- el cambio de colores debe seguir una secuencia apropiada
fun secuenciaColor: Color -> Color {
	// Color <: iden devuelve las TUPLAS de `iden` que empiezan con un Color
	// es decir, devuelve (Rojo, Rojo), (Amarillo, Amarillo), etc.
     (Color <: iden) + (Rojo-> Verde) + (Verde-> Amarillo) + (Amarillo -> Rojo)
 }

-- el semaforo soli puede cambiar su luz
pred cambioLuz(t,t1: Time,s:Semaforo ){ some c, c1: Color | (c -> t) in s.situacion 
                                    and (c1-> t1) in s.situacion and (c-> c1) in secuenciaColor }


-- relacion entre las estampillas de tiempo
fact traces{ 
    all s:Semaforo | Rojo -> ord/first in s.situacion
    all s:Semaforo, t:Time - ord/last | let t1= t.next | cambioLuz[t,t1,s]
}

-- el semáforo comienza en color Rojo
pred init[t:Time,s: Semaforo] { Rojo -> t in s.situacion}

pred buscar{some s: Semaforo |Amarillo -> ord/last in s.situacion} 

run buscar  for 1 Semaforo, 8 Time
