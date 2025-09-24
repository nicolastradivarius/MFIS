// Determine que signaturas o campos tienen sentido ser mutables, y agregar 'var' donde sea.

sig Valor {}

// Puede haber varios buffers
sig Buffer {
	// sucesor al buffer
	succ: one Buffer,
	// tiene sentido que el contenido de un buffer vaya cambiando con los pasos.
	// IMPORTANTE el buffer solo almacena hasta un valor
	var contenido: lone Valor
}

// tiene sentido que Leer y Escribir sean mutables pues a medida que avanzan los pasos,
// va cambiando lo que se quiere leer o escribir en un buffer. Ej: en el primer paso quiero 
// escribir un valores, en el siguiente leerlo, y en el siguiente escribir uno mas.
one var sig leer, escribir in Buffer {}

// similar a una mesa redonda unidireccional: los buffers son alcanzables uno al otro.
// desde 'b' puedo alcanzar a todos los demas buffers a traves del sucesor.
// (OJO) no quiere decir que desde b llegue a todos, sino que voy yendo de sucesor
// en sucesor.
fact circular {
	all b : Buffer | Buffer in b.^succ
}

fact init {
	leer = escribir
	no contenido
}

pred enviar [v : Valor] {
	no escribir.contenido
	contenido’ = contenido + (escribir -> v)
	escribir’ = escribir.succ
	leer’ = leer
}

pred recibir [v : Valor] {
	some leer.contenido
	v = leer.contenido
	contenido’ = contenido - (leer -> v)
	escribir’ = escribir
	leer’ = leer.succ
}

pred estable {
	contenido’ = contenido
	escribir’ = escribir
	leer’ = leer
}

fact traces {
	always (estable or some v : Valor | enviar[v] or recibir[v])
}


----- (a) Validar operaciones de cambio -----

run default {} for 3..10 steps

// RECORDAR busca que en el paso 1 se cumpla enviar[skolem v]
run enviar for 2..7 steps

check enviarSignificaQueElBufferEstaVacio {
	always {
		all v: Valor |
			enviar[v] implies (#escribir.contenido = 0)
	}
}

check enviarIncrementaElContenido {
	always {
		all v: Valor |
			enviar[v] implies (#escribir.contenido' = 1)
	}
}

// Si un valor es enviado a un buffer, ningun otro buffer lo tendra.
// Encuentra los mismos contraejemplos que los de noDataDuplication
check valorEnviadoEsUnico {
	always {
		all v: Valor | 
			enviar[v] implies
				(no b: Buffer - escribir | v in b.contenido)
	}
}

// enviar y recibir al mismo tiempo de buffers
run enviarYRecibir {
	eventually {
		some v: Valor | enviar[v] and recibir[v]
	}
}

run recibirCasoExito1 {
	eventually {
		some v: Valor | recibir[v]
	}
}

check recibirNoFunciona {
	always {
		all v: Valor | not recibir[v]
	}
}

run enviarYRecibir2 {
	some v: Valor | (enviar[v]; recibir[v]; enviar[v]; enviar[v])
}

// un valor en un bufer puede mantenerse de forma indeterminada
run valorParaSiempre {
	eventually {
		some v: Valor, b: Buffer | 
			v in b.contenido and
			always v in b.contenido
	}
} for 3..7 steps

-------- (b) Validar propiedades del modelo

// No hay un mismo valor en dos buffers distintos.
// Aunque tranquilamente podria ocurrir.
check noDataDuplication1 {
	always {
		all disj b1, b2: Buffer |
			b1.contenido & b2.contenido = none
	}
}

check noDataDuplication2 {
	always {
		no v: Valor, disj b1, b2: Buffer |
			v in b1.contenido and
			v in b2.contenido
	}
}

// no se usa un mismo buffer para leer y escribir al mismo tiempo.
check RolesDistintos {
	always {
		leer != escribir
	}
}

// El numero de valores cargados en el sistema no excede a la cantidad de buffers
check valoresNoSuperaBuffers {
	always {
		#Buffer.contenido <= #Buffer
	}
}


// un buffer siempre estara vacio despues de que se llame a la operacion recibir
check bufferVacioDespuesDeRecibirVersion1 {
	always {
		all v: Valor | some b: Buffer | 
			(v in b.contenido and recibir[v]) implies no b.contenido'
	}
}

check bufferVacioDespuesDeRecibirVersion2 {
	all v: Valor |
		eventually {
			recibir[v] iff 
				(some b: Buffer | v in b.contenido and after no b.contenido')
		}
}
