var sig Archivo {} // es mutable por vaciar[]
var sig Papelera in Archivo {}

pred borrar[a: Archivo] {
	// precondicion: el archivo no está en la papelera
	a not in Papelera and// en el estado actual, no en todos
	// postcondiciones
	Papelera' = Papelera + a and // la papelera del proximo estado es la que tengo en el estado corriente + el archivo
	// marco: mantengo aquellas cosas que son mutables
	Archivo' = Archivo
}

pred restaurar[a: Archivo] {
	// precondicion: el archivo está en la papelera
	a in Papelera and
	// postcondicion
	Papelera' = Papelera - a and
	// marco
	Archivo' = Archivo // los archivos siguen siendo los mismos
}

// los archivos deben dejar de existir luego de la operacion
pred vaciar[] {
	some Papelera and
	no Papelera' and
	Archivo' = Archivo - Papelera // el conjunto nuevo de archivos es el que tenía, sacando los archivos que estaban en la papelera
}

pred noHacerNada[] {
	Papelera' = Papelera and
	Archivo' = Archivo
}

fact comienzo {
	no Papelera
}

fact comportamiento {
	// para todos los estados de mi instancia, siempre hay un archivo que borro, restauro, vacío la papelera, o no hago nada
	always {
		some a: Archivo | borrar[a] or restaurar[a] or vaciar[] or noHacerNada[]
	}
}

// hay algun archivo que se restaure antes de que se vacíe la papelera
run restaurarAntesDeVaciar {
	eventually {
		// hay algun archivo en que se restaura y en el estado siguiente se vacia la papelera
		some a: Archivo | restaurar[a] and after vaciar[]
	}
}

// Afirmo que si restauro un archivo fue porque lo borré en algun momento
assert restaurarDespuesDeBorrar {
	always {
		// para todo archivo, si lo restauro, entonce alguna vez lo borré
		all a: Archivo | restaurar [a] implies once borrar[a]
	}
}

// probar que todas las instancias con minimo 3 y maximo 15 pasos se cumple la propiedad.
check restaurarDespuesDeBorrar for 3..15 steps

// si el estado inicial fuera tal que contuviera archivos en la papelera, entonces sí
// va a encontrar un contraejemplo, particularmente un archivo que esté en la papelera
// ya que nunca antes se había borrado.
