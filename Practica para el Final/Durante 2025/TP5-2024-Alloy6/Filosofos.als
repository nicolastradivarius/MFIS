
sig Filosofo {  
	izquierda: one Tenedor, 
	derecha: one Tenedor,
	var posee: set Tenedor
}

sig Tenedor { }

// agregamos dos signaturas de Comer y Pensar para indicar que un filosofo esta 
// comiendo o pensando
var sig Comiendo, Pensando, QuiereComer in Filosofo {}


/**  todos los filosofos y los tenedores forman una sola mesa redonda **/
fact { 
	all f: Filosofo | #Filosofo = #(f.^(izquierda.(~derecha))) 
}

/** Hay al menos dos filosofos y la cantidad de Tenedores es igual a la de Filósofos */
fact {
	#Filosofo = #Tenedor and 
	#Filosofo >= 2
}

/** Cada filosofo tiene dos tenedores diferentes. **/
fact {
	all f: Filosofo | f.derecha & f.izquierda = none
}

/** no hay dos filosofos con el mismo tenedor del mismo lado **/
fact {
	all disj f1, f2: Filosofo | 
		f1.derecha & f2.derecha = none and 
		f1.izquierda & f2.izquierda = none
}

fact "no hay dos filosofos que posean el mismo tenedor" {
	always {
		no t: Tenedor, disj f1, f2: Filosofo | 
			t in f1.posee and
			t in f2.posee	
	}
}

fact "un filosofo quiere comer si y solo si tiene solamente un tenedor en la mano" {
	always {
		all f: Filosofo | 
			f in QuiereComer iff one f.posee
	}
}

fact "un filosofo esta comiendo si y solo si tiene dos tenedores en la mano" {
	always {
		all f: Filosofo |
			f in Comiendo iff #f.posee = 2
	}
}

fact "un filosofo esta pensando si y solo si no tiene tenedores en la mano" {
	always {
		all f: Filosofo |
			f in Pensando iff no f.posee
	}
}

fact "los tenedores que puede poseer un filosofo son los de su lados" {
	always {
		all f: Filosofo |
			f.posee in f.(izquierda+derecha)
	}
}

fact "un filosofo esta en un unico estado" {
	always {
		no Comiendo & Pensando
		no Comiendo & QuiereComer
		no Pensando & QuiereComer
	}
}

fact init {
	// al principio todos los filosofos estan pensando
	Pensando = Filosofo and
	no Comiendo and
	no posee
}

fact traces {
	always {
		hacerNada or
		(some f: Filosofo | tomarTenedor[f] or soltarTenedores[f])
	}
}


run default {eventually some posee} for exactly 5 Filosofo, 5 Tenedor

-------- Predicados de Cambio ----------


pred tomarTenedor [f: Filosofo] {
	some t: Tenedor |
		t not in f.posee and
		posee' = posee + (f->t)
}

pred soltarTenedores [f: Filosofo] {
	some disj t1, t2: Tenedor |
		( (f->t1) + (f->t2) in posee ) and
		posee' = posee - (f->t1) - (f->t2)
}

pred hacerNada [] {
	Comiendo' = Comiendo
	Pensando' = Pensando
	QuiereComer' = QuiereComer
	posee' = posee
}


--------------------------


run tomarTenedorCasoExito1 {
	eventually {
		some f: Filosofo | tomarTenedor[f]
	}
} for exactly 5 Filosofo, 5 Tenedor, 4..10 steps

// eventualmente un filosofo toma (por primera vez) un tenedor, luego toma otro, y luego
// los suelta.
run tomarYSoltarTenedorCasoExito2 {
	eventually {
		some f: Filosofo | (tomarTenedor[f]; tomarTenedor[f]; soltarTenedores[f])
	}
} for exactly 5 Filosofo, 5 Tenedor, 4..10 steps

// eventualmente un filosofo toma un tenedor e inmediatamente suelta los dos.
// imposible porque no puede soltar los dos, si solo tiene uno
run tomarYSoltarTenedorCasoNoExito1 {
	some f: Filosofo | (eventually tomarTenedor[f] and after soltarTenedores[f])
//	some f: Filosofo | (eventually tomarTenedor[f]); soltarTenedores[f])
} for exactly 5 Filosofo, 5 Tenedor

// reformulacion del caso de no exito 1: trasladamos lo que queremos que ocurra al primer
// paso.
run tomarYSoltarTenedorCasoExito3 {
	some f: Filosofo | 
		tomarTenedor[f] and after soltarTenedores[f] 
} for exactly 5 Filosofo, 5 Tenedor

// chequear en todos los pasos, si el filosofo quiere comer, es porque en pasos anteriores
// estuvo pensando y tomo un tenedor.
check tomarTenedorQuiereComer1 {
	always {
		all f: Filosofo | 
			-- si en el paso actual quiere comer
			(f in QuiereComer) implies 
				-- entonces en algun paso previo estuvo pensando y tomo un tenedor
				(once f in Pensando and once tomarTenedor[f])
	}
}

check tomarTenedorQuiereComer2 {
	always {
		all f: Filosofo |
			-- si en el paso actual esta pensando y toma un tenedor
			(f in Pensando and tomarTenedor[f]) implies
				-- entonces en el paso posterior estara queriendo comer
				(after f in QuiereComer)
	}
}

// Si un filosofo esta pensando, y toma dos tenedores, pasara a estar pensando.
// en un paso toma un tenedor, en otro paso toma el otro, y entonces en dos pasos
// esta comiendo. Esto se muestra con after (after ...) ya que son dos pasos.
check tomarTenedoresComiendo1 {
	always {
		all f: Filosofo |
			-- si en el paso actual esta pensando, toma un tenedor, y en el paso
			-- siguiente toma otro tenedor
			(f in Pensando and tomarTenedor[f] and after tomarTenedor[f]) implies
				-- entonces, a partir del paso actual, dos pasos despues esta comiendo.
				(after (after f in Comiendo))
	}
}

// Si un filosofo tenia sus tenedores y luego dejo de tenerlos, fue por la operacion de soltar.
check tenedoresSoltados {
	always {
		all f: Filosofo |
			-- si alguna vez tuvo dos tenedores, y en el paso actual no los tiene
			(once #f.posee = 2 and no f.posee) implies
				-- entonces en algun paso anterior tuvo que haberlos soltado
				(once soltarTenedores[f])
	}
}


---------------- 


run nadiePuedeComer1 {
	eventually {
		all f: Filosofo | one f.posee
	}
} for exactly 5 Filosofo, 5 Tenedor

run nadiePuedeComer2 {
	eventually {
		QuiereComer = Filosofo
	}
} for exactly 5 Filosofo, 5 Tenedor

check deadlock {
	always {
		(QuiereComer = Filosofo) implies (always QuiereComer = Filosofo)
	}
} for exactly 5 Filosofo, 5 Tenedor
