sig Persona {}

sig Habitante in Persona {}

sig Turista in Persona {}

one sig Ciudad {
	-- el campo habitantes es innecesario porque se puede modelar con el campo
	-- poblacion y la signatura Habitante.
	var habitantes: set Persona,
	var poblacion: set Persona,
	var esperandoIngreso: lone Persona
}

// mínima cantidad de personas
fact {#Habitante > 1 and #Turista > 1}

// relación turistas - habitantes
fact {
	always {
		#(Ciudad.poblacion & Habitante) <= #(Ciudad.poblacion & Turista)
	}
}

run default {}

// Caso donde hay una persona que no es ni turista ni habitante.
// Encuentra instancias, la primera es tal que Persona0 no es habitante ni turista.
run personaRara {
	some (Persona - Habitante - Turista)
}

// Caso donde una persona es habitante y turista al mismo tiempo.
// Encuentra instancias, lo cual es un problema y contradice la especificacion.
run habitanteYTurista {
	some p: Persona | (p in Habitante) and (p in Turista)
}

// Caso donde una persona esta dentro de la ciudad y esperando para ingresar a la vez.
// Encuentra instancias, lo cual no tiene sentido porque la persona ya ingreso a la ciudad.
run adentroYAfuera {
	some p: Persona | (p in Ciudad.poblacion) and (p in Ciudad.esperandoIngreso)
}

// Vemos si es posible que la ciudad quede vacia.
// Resultado: no es posible. Deberia serlo.
run ciudadVacia {
	no Ciudad.poblacion
} for 10

// Caso donde hay habitantes que no son poblacion de la ciudad.
// Encuentra instancias. La primer instancia muestra que Persona2 es habitante, pero no
// es parte de la poblacion, e incluso esta esperando para ingresar.
run habitantesNoPobladores {
	some p: Persona | (p in Ciudad.habitantes) and (p not in Ciudad.poblacion)
}

// Verificamos que solo los turistas esperen para ingresar.
// Encuentra contraejemplos en los que la persona esperando es habitante.
// Son contraejemplos validos pues ellos tambien deben tramitar el ingreso.
check turistasSoloRequierenEsperar {
	(Ciudad.esperandoIngreso in Turista - Habitante)
}

run habitanteEsperandoParaIngresar {
	some h: Habitante | (h in Ciudad.esperandoIngreso)
}

// Caso donde ingresan mas de dos personas a la ciudad.
// El puente solo admite una persona con lo cual esta situacion no deberia ocurrir.
// Encuentra instancias.
run ingresaronMasDeUno {
	// ponemos 'one' porque la ciudad no puede estar vacia.
	// la prueba podria y deberia hacerse con 'no'
	one Ciudad.poblacion and after #Ciudad.poblacion = 3
}

// Caso donde ingresa un turista a la ciudad cuando hay mas turistas dentro que habitantes.
run turistaIngresaIlegalmente {
	eventually {
		(some t: Turista - Habitante | t in Ciudad.poblacion) and
		(#Ciudad.poblacion & Turista > #Ciudad.poblacion & Habitante)
	}
}
