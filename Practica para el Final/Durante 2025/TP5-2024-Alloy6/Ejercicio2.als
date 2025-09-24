// (3) Necesito que Archivo sea mutable para poder vaciar la papelera efectivamente y que los
// archivos que estan en ella desaparezcan. De otro modo, siendo signatura estatica, en todos
// los pasos habra siempre la misma cantidad de atomos de Archivo, haciendo imposible
// el vaciado.
var sig Archivo {}

one sig Papelera {
	var contenido: set Archivo
}

pred borrar[a:Archivo] {
	// el archivo no esta en el contenido de la papelera
	(Papelera -> a) not in contenido
	// el contenido en el paso siguiente es igual a todo lo que tenia antes + el archivo
	contenido’ = contenido + (Papelera ->a)
	Archivo' = Archivo
}

pred restaurar[a:Archivo] {
	a in Papelera.contenido
	contenido’ = contenido - (Papelera -> a)
	Archivo' = Archivo
}

pred vaciar[] {
	some Papelera.contenido
	no Papelera.contenido’
	Archivo' = Archivo - Papelera.contenido
}

pred noHacerNada[] {
	contenido’=contenido
	Archivo' = Archivo
}

fact comportamiento {
	no Papelera.contenido and
	always { (some a: Archivo | borrar[a] or restaurar[a]) or vaciar or noHacerNada}
}

run default {}


// (a) Todo archivo que es restaurado, previamente fue borrado
check propiedadA {
	// en todos los pasos se cumple que...
	always {
		// para todos los archivos... 
		// si se restaura un archivo entonces en algun paso anterior se borro
		all a: Archivo | restaurar[a] implies once borrar[a]
	}
} for 5 Archivo

// (b) Todo archivo borrado no puede restaurarse luego de vaciar la papelera
check propiedadB {
	always {
		// para todos los archivos de la papelera ..
		// si en el paso i se vacia la papelera, entonces en todos los pasos >= i sucede
		// que no se podra ejecutar la operacion de restaurar ese archivo.
		all a: Papelera.contenido | vaciar implies always (not restaurar[a])
	}
}

// todo archivo que esta en la papelera es porque se borro alguna vez
check archivoEnPapeleraEsPorqueSeBorro {
	always {
		all a: Papelera.contenido | once borrar[a]
	}
}

// (c) Si todos los archivos estan en la papelera y esta se vacia, ent. no existen mas archivos
check propiedadC {
	always {
		// (...) entonces no habra atomos en Archivo en el estado posterior al vaciado.
		(Papelera.contenido = Archivo and vaciar) implies no Archivo'
	}
}
