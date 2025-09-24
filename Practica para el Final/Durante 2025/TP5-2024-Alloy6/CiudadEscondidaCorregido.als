abstract sig Persona {}

sig Habitante, Turista extends Persona {}

one sig Ciudad {
	var poblacion: set Persona,
	var esperandoIngreso: lone Persona
}

// mínima cantidad de personas
fact {#Habitante > 1 and #Turista > 1}

// relación turistas - habitantes
fact {
	always {
		#(Ciudad.poblacion & Habitante) >= #(Ciudad.poblacion & Turista)
	}
}

fact "no hay personas dentro de la ciudad y esperando para entrar al mismo tiempo" {
	always {
		no p: Persona | p in Ciudad.poblacion and p in Ciudad.esperandoIngreso
	}
}

fact init {
	#Ciudad.poblacion = 5 and
	#Ciudad.esperandoIngreso = 0
}

fact traces {
	always {
		registrarse or ingresar or egresar
	}
}

pred registrarse[] {
	some p: Persona |
		(p not in Ciudad.poblacion) and
		(p not in Ciudad.esperandoIngreso) and
		(Ciudad.esperandoIngreso' = Ciudad.esperandoIngreso + p) and
		poblacion' = poblacion
}

pred ingresar [] {
	some p: Persona |
		(p in Ciudad.esperandoIngreso) and
		(p not in Ciudad.poblacion) and
		(Ciudad.poblacion' = Ciudad.poblacion + p) and
		(Ciudad.esperandoIngreso' = Ciudad.esperandoIngreso - p)
}

pred egresar [] {
	some p: Persona |
		(p in Ciudad.poblacion) and
		(Ciudad.poblacion' = Ciudad.poblacion - p) and
		(Ciudad.esperandoIngreso' = Ciudad.esperandoIngreso)
}

run default {} for 10 Persona, 3..4 steps

// Caso donde hay una persona que no es ni turista ni habitante.

run personaRara {
	some (Persona - Habitante - Turista)
} for 10

// Caso donde una persona es habitante y turista al mismo tiempo.

run habitanteYTurista {
	some p: Persona | (p in Habitante) and (p in Turista)
} for 10

// Caso donde una persona esta dentro de la ciudad y esperando para ingresar a la vez.

run adentroYAfuera {
	some p: Persona | (p in Ciudad.poblacion) and (p in Ciudad.esperandoIngreso)
} for 10

// Vemos si es posible que la ciudad quede vacia.

run ciudadVacia {
	no Ciudad.poblacion
} for 10


// Verificamos que solo los turistas esperen para ingresar.

check turistasSoloRequierenEsperar {
	(Ciudad.esperandoIngreso in Turista)
} for 10

run habitanteEsperandoParaIngresar {
	some h: Habitante | (h in Ciudad.esperandoIngreso)
} for 10

// Caso donde ingresan mas de dos personas a la ciudad.
// El puente solo admite una persona con lo cual esta situacion no deberia ocurrir.
run ingresaronMasDeUno {
	// ponemos 'one' porque la ciudad no puede estar vacia.
	// la prueba podria y deberia hacerse con 'no'
	one Ciudad.poblacion and after #Ciudad.poblacion = 3
} for 10

// Caso donde ingresa un turista a la ciudad cuando hay mas turistas dentro que habitantes.
run turistaIngresaIlegalmente {
	no Ciudad.poblacion and
	eventually {
		(some t: Turista | t in Ciudad.poblacion) and
		(#Ciudad.poblacion & Turista > #Ciudad.poblacion & Habitante)
	}
} for 10

run registrarseCasoExito1 {
	eventually registrarse
} for 10 Persona

// Chequeamos si siempre que se registra una persona, en el paso siguiente ingresa.
// Encuentra contraejemplos en los que sucede un egreso mientras la persona esta en espera.
check registrarEInmediatamenteIngresar {
	always {
		registrarse implies after ingresar
	}
} for 10 Persona

check IngresarIncrementaPoblacion {
	always {
		(#Ciudad.poblacion = 6 and ingresar) implies
			(after #Ciudad.poblacion = 7)
	}
} for 10 Persona

check egresarDecrementaPoblacion {
	always {
		(#Ciudad.poblacion = 6 and egresar) implies
			(after #Ciudad.poblacion = 5)
	}	
} for 10 Persona

// Caso donde ocurren ambas operaciones en simultaneo
run registrarEIngresar {
	eventually {
		registrarse and ingresar
	}
} for 10 Persona

run registrarYEgresar {
	eventually {
		registrarse and egresar
	}
} for 10 Persona

run ingresarYEgresar{
	eventually {
		ingresar and egresar
	}
} for 10 Persona, 5..15 steps



// Validar si es posible que un habitante este en la ciudad y en el proximo estado ya no
// lo este.
run habitanteSeVa {
	some h: Habitante | (h in Ciudad.poblacion) and after (h not in Ciudad.poblacion)
} for 10 Persona

run habitanteSeVa2 {
	eventually {
		(some h: Habitante | h in Ciudad.poblacion and after h !in Ciudad.poblacion)
	}
} for 10 Persona

// Alloy eligio de skolem a Turista0, que se registro, ingreso a la ciudad y en el paso
// siguiente se fue.
run habitanteSeVa3 {
	registrarse; ingresar; egresar
} for 10 Persona

// Validar si es posible que un turista que está en la ciudad no pueda abandonar la ciudad 
run turistaNoPuedeIrse {
	eventually {
		some t: Turista | t in Ciudad.poblacion and always t in Ciudad.poblacion
	}
} for 10 Persona

// En las instancias se puede notar que siempre hay algun turista que se queda indefinidament
run turistaNoPuedeIrse2 {
	let turistas = Ciudad.poblacion & Turista | 
		always some turistas and
		always (Ciudad.poblacion & Turista = turistas)
} for 10 Persona, 5..20 steps

// En todos los estados, si no hay habitantes en la ciudad y en la cola de ingreso hay
// turistas y habitantes, entonces en el siguiente estado ingresará un habitante a la ciudad
// (la idea es que el turista no puede entrar porque hay menos -no hay- habitantes
// dentro de los muros que turistas)
check ciudadVaciaSiempreEntraHabitante {
	always {
		(
			-- si en el paso actual no hay poblacion y hay algun turista o habitante
			-- esperando para ingresar (recordar solo puede haber una persona)
			(no Ciudad.poblacion) and 
			some (Ciudad.esperandoIngreso & (Turista+Habitante))
		)
		implies
		(
			-- entonces en ese mismo paso se da la operacion de ingreso (de la persona
			-- que estaba esperando) y la poblacion del paso siguiente tiene un habitante
			ingresar and 
			one (Ciudad.esperandoIngreso & Habitante) and
			one (Ciudad.poblacion' & Habitante)
		)
	}
} for 10 Persona, 20 steps

// Si se le da prioridad a la operación de ingreso por sobre las otras, ¿cambia la
// respuesta del analizador con respecto a la propiedad del inciso anterior? Realice la
// modificación y muestre el resultado dado por el analizador.

fact "el ingreso tiene prioridad" {
	always {
		some Ciudad.esperandoIngreso implies 
			after (ingresar and not egresar and not registrarse)
	}
}

// No cambia la respuesta del analizador con respecto al chequeo de la propiedad.
// Esto ocurre porque, dada la situacion en la que se encuentra, no queda otra opcion
// que realizar la operacion de ingreso, tenga esta prioridad o no. Claramente si la ciudad
// esta vacia y hay una persona esperando para ingresar, la unica operacion viable es 
// ingresar, porque el registrarse ya viene efectuada, y no se puede efectuar egresar porque
// no hay personas en la ciudad.
