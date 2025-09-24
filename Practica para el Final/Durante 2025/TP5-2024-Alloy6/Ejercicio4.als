/**
Reformule el ejercicio anterior para considerar varias papeleras en lugar de una sola.
Tenga en cuenta que deben considerarse algunas restricciones adicionales, como 
asegurarse que los archivos no esten en varias papeleras al mismo tiempo.
*/

// (3) Necesito que Archivo sea mutable para poder vaciar la papelera efectivamente y que los
// archivos que estan en ella desaparezcan. De otro modo, siendo signatura estatica, en todos
// los pasos habra siempre la misma cantidad de atomos de Archivo, haciendo imposible
// el vaciado.
var sig Archivo {}

some sig Papelera {
	var contenido: set Archivo
}

fact "un mismo archivo nunca podra estar en dos papeleras" {
	always {
		all disj p1, p2: Papelera |
			no p1.contenido & p2.contenido
	}
}

// Predicado que modela el comportamiento de enviar un archivo 'a' a la papelera 'p'
pred borrar[a:Archivo, p: Papelera] {
	// el archivo no esta en el contenido de la papelera
	(p -> a) not in contenido
	// el contenido en el paso siguiente es igual a todo lo que tenia antes + el archivo
	contenido’ = contenido + (p ->a)
	Archivo' = Archivo
}

// Predicado que modela el comportamiento de restaurar un archivo 'a' de la papelera 'p'
pred restaurar[a: Archivo, p: Papelera] {
	a in p.contenido
	contenido’ = contenido - (p -> a)
	Archivo' = Archivo
}

// Predicado que modela el comportamiento de vaciar enteramente una papelera 'p'.
// Los archivos que estaban en esa papelera dejan de existir en el paso siguiente.
pred vaciar[p: Papelera] {
	some p.contenido
	no p.contenido’
	// en el proximo paso, el conjunto de archivos se disminuye segun los que se vaciaron
	Archivo' = Archivo - p.contenido
	// el resto de las papeleras se mantiene invariante
	contenido’=contenido
}

// Predicado que modela el comportamiento de no realizar accion alguna en la transicion.
pred noHacerNada[] {
	contenido’=contenido
	Archivo' = Archivo
}

fact init {
	// al igual que cualquier predicado o hecho, esto es valido en el primer paso solamente
	no Papelera.contenido and
	// con always {} defino el comportamiento a lo largo de todos los pasos
	always { 
		(some a: Archivo, p: Papelera | 
			borrar[a, p] or restaurar[a, p] or vaciar[p]
		) or
		noHacerNada
	}
}

run default {#Papelera = 2} for 5 Archivo, 2 Papelera, 5..10 steps

run dosPapelerasConContenidoEventualmente {
	#Papelera = 2
	eventually {
		some disj p1, p2: Papelera | some p1.contenido and some p2.contenido
	}
}

run archivoEnDosPapeleras {
//	Si lo pido asi de una, lo estoy pidiendo para el estado inicial.
// 	Por culpa de la restriccion del comportamiento, no genera instancias porque las
//	papeleras no pueden tener contenido EN EL PRIMER ESTADO.
//	some a: Archivo, disj p1, p2: Papelera | (a in p1.contenido) and (a in p2.contenido)
//	Para solucionar esto, puedo pedir que eventualmente suceda en alguno de los pasos...
	eventually {
		some a: Archivo, disj p1, p2: Papelera | 
			(a in p1.contenido) and 
			(a in p2.contenido)
	}
}


// (a) Todo archivo que es restaurado, previamente fue borrado
check propiedadA {
	// en todos los pasos se cumple que...
	always {
		// para todos los archivos... 
		// si se restaura un archivo de una papelera 
		// entonces en algun paso anterior se borro y fue a parar a esa papelera
		all a: Archivo, p: Papelera | 
			restaurar[a, p] implies once borrar[a, p]
	}
}


// (b) Todo archivo borrado no puede restaurarse luego de vaciar la papelera
check propiedadB {
	always {
		// para todas las papeleras y todos sus archivos...
		// si en el paso i se vacia la papelera, entonces en todos los pasos >= i sucede
		// que no se podra ejecutar la operacion de restaurar sus archivos.
		all p: Papelera, a: p.contenido | vaciar[p] implies always (not restaurar[a, p])
	}
} for 10


// todo archivo que esta en la papelera es porque se borro alguna vez
check archivoEnPapeleraEsPorqueSeBorro {
	always {
		all p: Papelera, a: p.contenido | once borrar[a, p]
	}
}


// (c) Si todos los archivos estan en la papelera y esta se vacia, ent. no existen mas archivos
check propiedadC {
	always {
		// para todas las papeleras, si todos los archivos estan en ella, entonces...
		// ... en el proximo paso no habra mas archivos.
		all p: Papelera | (p.contenido = Archivo and vaciar[p]) implies no Archivo'
	}
} for 10 but 1..15 steps
