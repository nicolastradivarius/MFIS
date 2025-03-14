/*
Cuatro amigos decidieron concurrir juntos a hacerse su primer tatuaje en la misma casa
de tatuado. Cada uno eligió tatuarse en una parte del cuerpo distinta. Asimismo, cada 
tatuaje posee un motivo distinto, y demandó un tiempo de tatuado diferente.
*/

abstract sig Amigo {
	tatuaje: one Tatuaje,
	parteCorporal: one ParteCorporal
}

abstract sig Tatuaje {
	tiempoInsumo: one Hora
}

abstract sig ParteCorporal {}

abstract sig Hora {}

one sig Marina, Juan, Silvia, Ernesto extends Amigo {}

one sig Hombro, Tobillo, Espalda, Antebrazo extends ParteCorporal {}

one sig Serpiente, Delfin, Unicornio, Corazon extends Tatuaje {}

one sig Dieciseis, Ocho, Cuatro, Cinco extends Hora {}

---- Restricciones Generales ----

//Hay exactamente cuatro amigos
fact {#Amigo = 4}

//Cada amigo tiene un tatuaje diferente
fact {no disj a1, a2: Amigo | (a1.tatuaje = a2.tatuaje)}

//Cada amigo se tatuó en una parte distinta del cuerpo
fact {no disj a1, a2: Amigo | (a1.parteCorporal = a2.parteCorporal)}

//Cada tatuaje llevó un tiempo distinto para realizarse
fact {all disj t1, t2: Tatuaje | (t1.tiempoInsumo != t2.tiempoInsumo)}

---- Restricciones especificas ----

//Marina lleva su tatuaje en el hombro
fact {one a: Amigo | (a = Marina) and (a.parteCorporal = Hombro)}

//Se necesito el doble de tiempo para tatuar la serpiente que para el delfin
fact {one disj t1, t2: Tatuaje | 
	(t1 = Serpiente) and
	(t2 = Delfin) and
	dobleTiempo[t1.tiempoInsumo, t2.tiempoInsumo]
}

//Juan se tatuo un corazon
fact {one a: Amigo | (a = Juan) and (a.tatuaje = Corazon)}

//El tatuaje realizado en el tobillo de alguien insumió 16 horas de trabajo
fact {one a: Amigo | (a.parteCorporal = Tobillo) and (a.tatuaje.tiempoInsumo = Dieciseis)}

//Silvia se tatuo un unicornio
fact {one a: Amigo | (a = Silvia) and (a.tatuaje = Unicornio)}

//El tatuaje de Ernesto llevó 8 horas de trabajo
fact {one a: Amigo | (a = Ernesto) and (a.tatuaje.tiempoInsumo = Ocho)}

//Hacer el tatuaje que alguien lleva en la espalda le insumió al tatuador la mitad de
//tiempo que lo que le insumio hacer el tatuaje de Silvia.
fact {one disj a1, a2: Amigo | 
	(a1.parteCorporal = Espalda) and
	(a2 = Silvia) and
	mitadTiempo[a1.tatuaje.tiempoInsumo, a2.tatuaje.tiempoInsumo]
}

//Algun amigo se tatuó el antebrazo
fact {one a: Amigo | (a.parteCorporal = Antebrazo)}

//Dos de los tatuajes insumieron 4 y 5 horas de trabajo respectivamente.
fact {one disj t1, t2: Tatuaje | (t1.tiempoInsumo = Cuatro) and (t2.tiempoInsumo = Cinco)}


---- Predicados & Funciones ----

//Determina que h1 es el doble de tiempo que h2
pred dobleTiempo [h1, h2: Hora] {
	((h1 = Dieciseis) and (h2 = Ocho)) or
	((h1 = Ocho) and (h2 = Cuatro))
}

//Determina que h1 es la mitad de tiempo que h2 (o lo que es lo mismo, que h2 es el doble que h1)
pred mitadTiempo [h1, h2: Hora] {
	dobleTiempo[h2, h1]
}

---- Instancias ----

run {} for 4
