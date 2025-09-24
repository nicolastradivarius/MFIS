sig Barco { }

sig Auto { }

abstract sig EstadoPuente { }

one sig Elevado, Bajo extends EstadoPuente { }

one sig Puente {
	var estado: one EstadoPuente,
	var barcosEnEspera: set Barco,
	var autosEnPuente: lone Auto,
	var autosEnEspera: set Auto
}

run default {}

run algunosAutos {
	eventually some autosEnPuente and 
	eventually #autosEnEspera = 3
} for 3..8 steps

fact "no hay un mismo auto cruzando el puente y esperando para cruzarlo" {
	always {
		no autosEnPuente & autosEnEspera
	}
}

run {
	eventually some a: Auto | a in Puente.autosEnEspera and a in Puente.autosEnPuente
} for 10

run autoEnPuenteConPuenteElevado {
	eventually some a: Auto | a in Puente.autosEnPuente and Puente.estado in Elevado
}

fact "no hay autos cruzando el puente cuando esta elevado" {
	always {
		no a: Auto | (Puente.estado in Elevado) and (a in Puente.autosEnPuente)
	}
}

fact "si el puente esta elevado, los autos esperando se quedaran esperando hasta que baje" {
	always {
		Puente.estado in Elevado implies (autosEnEspera' = autosEnEspera)
	}
}

fact "en cada instancia existen al menos dos barcos y al menos dos autos" {
	always {
		#Barco >= 2 and
		#Auto >= 2
	}
}

fact init {
	#barcosEnEspera >= 2 and
	#autosEnEspera >= 2 and
	Puente.estado = Bajo
}

fact traces {
	always {
		cambiaPuente or
		llegaBarco or
		llegaAuto or
		subeAuto or
		bajaAuto or
		cruzaBarco
	}
}

pred cambiaPuente [] {
//	(Puente.estado = Bajo iff Puente.estado' = Elevado)
	(Puente.estado = Bajo implies Puente.estado' = Elevado) and
	(Puente.estado = Elevado implies Puente.estado' = Bajo) and
	-- invariantes
	(barcosEnEspera' = barcosEnEspera) and
	(autosEnEspera' = autosEnEspera)
}

pred llegaAuto [] {
	(some a: Auto |
		a not in Puente.autosEnEspera and
		Puente.autosEnEspera' = Puente.autosEnEspera + a
	) and
	barcosEnEspera' = barcosEnEspera and
	autosEnPuente' = autosEnPuente and
	Puente.estado' = Puente.estado
}

pred llegaBarco [] {
	(some b: Barco |
		b not in Puente.barcosEnEspera and
		Puente.barcosEnEspera' = Puente.barcosEnEspera + b
	) and
	autosEnEspera' = autosEnEspera and
	autosEnPuente' = autosEnPuente and
	Puente.estado' = Puente.estado		
}

pred subeAuto [] {
	(some a: Puente.autosEnEspera |
--		a not in Puente.autosEnPuente and
		Puente.estado in Bajo and
		Puente.autosEnPuente' = Puente.autosEnPuente + a and
		Puente.autosEnEspera' = Puente.autosEnEspera - a
	) and
	barcosEnEspera' = barcosEnEspera and
	Puente.estado' = Puente.estado
}

pred bajaAuto [] {
	(some a: Puente.autosEnPuente |
		Puente.estado in Bajo and
		Puente.autosEnPuente' = Puente.autosEnPuente - a
	) and
	autosEnEspera' = autosEnEspera and
	barcosEnEspera' = barcosEnEspera and
	Puente.estado' = Puente.estado
}

pred cruzaBarco [] {
	(some b: Puente.barcosEnEspera |
		Puente.barcosEnEspera' = Puente.barcosEnEspera - b and
		Puente.estado = Elevado
	) and
	autosEnEspera' = autosEnEspera and
	autosEnPuente' = autosEnPuente
}

run llegaAutoCasoExito1 {
	eventually llegaAuto
}

// Si hay un auto en el puente, puede mantenerse sobre el puente en forma indeterminada.
run autoIndefinido {
	eventually {
		(some a: Auto | 
			a in Puente.autosEnPuente and 
			always (llegaAuto or llegaBarco)
		)
	}
} for 10
