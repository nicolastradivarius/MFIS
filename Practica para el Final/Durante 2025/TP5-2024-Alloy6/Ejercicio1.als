// los Archivos son mutables, o sea, los atomos que lo conforman van cambiando a lo largo
// del ciclo de vida de la instancia (los estados/pasos/steps).
var sig Archivo {}

var sig Papelera in Archivo {}

pred borrar[a:Archivo] {
	a not in Papelera
	Papelera' = Papelera + a
	Archivo'= Archivo
}

pred restaurar[a:Archivo] {
	a in Papelera
	Papelera' = Papelera - a
	Archivo'= Archivo
}

pred vaciar[] {
	some Papelera
	no Papelera'
	Archivo'= Archivo - Papelera
}

pred noHacerNada[] {
	Papelera'= Papelera
	Archivo'= Archivo
}

fact comportamiento {
	no Papelera and
	always { 
		(some a: Archivo | borrar[a] or restaurar[a]) or vaciar or noHacerNada
	}
}

run default {} for 5 steps


// (a) Todo archivo que es restaurado, previamente fue borrado
check propiedadA {
	// en todos los pasos se cumple que...
	always {
		// para todos los archivos... 
		// si se restaura un archivo entonces en algun paso anterior se borro
		all a: Archivo | restaurar[a] implies once borrar[a]
	}
} for 5 Archivo, 13 steps

// (b) Todo archivo borrado no puede restaurarse luego de vaciar la papelera
check propiedadB {
	always {
		// para todos los archivos de la papelera ..
		// si en el paso i se vacia la papelera, entonces en todos los pasos >= i sucede
		// que no se podra ejecutar la operacion de restaurar ese archivo.
		all a: Papelera | vaciar implies always not restaurar[a]
	}
}

// todo archivo que esta en la papelera es porque se borro alguna vez
check archivoEnPapeleraEsPorqueSeBorro {
	always {
		all a: Papelera | once borrar[a]
	}
}

// (c) Si todos los archivos estan en la papelera y esta se vacia, ent. no existen mas archivos
check propiedadC {
	always {
		// (...) entonces no habra atomos en Archivo en el estado posterior al vaciado.
		(Papelera = Archivo and vaciar) implies no Archivo'
	}
}
