sig Hombre { 
	afeita: set Hombre 
}

some sig Barbero extends Hombre {}

fact {
	Barbero.afeita = {h: Hombre | h not in h.afeita} 
}

fact "los hombres que no sean el barbero no pueden afeitar a otros hombres" {
	all h: Hombre - Barbero | no h2: Hombre - {h} | h2 in h.afeita
}

run default {}

// La solucion a la paradoja es que el barbero siempre es afeitado por otro barbero.

check barberoSiempreEsAfeitadoPorOtro {
	all b: Barbero | some b2: Barbero | b2 != b and b in b2.afeita
} for 10
