/**
Considere un puente levadizo sobre el que pasan autos cuando se encuentra bajo, permitiendo
tambien el paso de barcos (por debajo de el) cuando se encuentra elevado. Considere que en toda
instancia deben existir al menos dos barcos y al menos dos autos. Por cuestiones de seguridad, en
todo momento puede haber como maximo un auto sobre el puente.
*/

open util/ordering[Estado] as ord

sig Barco { }

sig Auto { }

abstract sig Puente { }

one sig Elevado, Bajo extends Puente { }

sig Estado {
	puente: one Puente,
	// cambiamos la multiplicidad a "set" para permitir que un barco cruce y deje de estar en el
	// conjunto de barcos esperando del estado anterior
	barcosEnEspera: set Barco,
	autosEnEspera: set Auto,
	// cambiamos la multiplicidad a "lone" para permitir que no haya autos en el puente cuando
	// está elevado.
	autosEnPuente: lone Auto
}

// agregamos este hecho para respetar el enunciado.
fact "en toda instancia hay al menos dos autos y dos barcos" {
	#Auto >= 2 and #Barco >= 2
}

run default {} for 6

