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
	barcosEnEspera: some Barco,
	autosEnEspera: set Auto,
	autosEnPuente: one Auto
}

---------------------- Validación del modelo ----------------------

run default {} for 6

// hay al menos dos autos y dos barcos.
// encuentra un contraejemplo en el que hay solo un barco y solo un auto.
check alMenosDosAutosYBarcos {
	#Auto >= 2 and #Barco >= 2
}

// cuando el puente esté elevado, que no haya ningun auto en él.
// No se verifica.
check puenteElevadoNoAutos {
	all e: Estado | e.puente = Elevado implies no e.autosEnPuente
}

// el puente estuvo bajo por dos estados continuos, y ningun auto pasó por el.
// al ser la relación `autosEnPuente` de multiplicidad 'one' con Auto, siempre va a haber algo.
// por ese motivo, alloy no encuentra instancias. De todas formas es probable que
// encuentre si esa multiplicidad fuera 'set' o 'lone' ya que no existe una operación de cruce.
// Viendo el inciso (d), es preferible que esto ocurr
run puenteBajoNadieCruza {
	some e1: Estado-ord/last | let e2 = e1.next | 
		(e1.puente = Bajo) and 
		(e2.puente = Bajo) and
		(some e1.autosEnEspera) and
		(no e2.autosEnPuente)
} for 9

// si el puente está elevado, y hay dos barcos esperando, en el proximo debe haber uno solo.
// Falla.
check barcoCruza {
	some e1: Estado - ord/last | let e2 = e1.next | 
		((e1.puente = Elevado) and (#(e1.barcosEnEspera) = 2)) implies
		(#(e2.barcosEnEspera) = 1)
}

run autosDandoVueltas {
	some a: Auto, e: Estado | a not in e.autosEnEspera
}

run autoDandoVueltasLlegaAPuente {
	some a: Auto, e1: Estado | let e2 = e1.next |
		(a not in e1.autosEnEspera) and (a in e2.autosEnEspera)
}
