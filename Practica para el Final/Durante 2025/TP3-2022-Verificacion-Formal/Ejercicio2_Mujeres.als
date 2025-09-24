abstract sig Habitante {
	afeita: set Habitante
}

sig Hombre, Mujer extends Habitante {}

one sig Barbero in Habitante {}

fact {
	Barbero.afeita = {h: Hombre | h not in h.afeita} 
}

fact "los hombres que no sean el barbero no pueden afeitar a otros hombres" {
	all h: Habitante - Barbero | no h2: Habitante - {h} | h2 in h.afeita
}

fact "las mujeres no necesitan afeitarse" {
	all m: Mujer - Barbero | no m.afeita
}

run default {}

run barberoAfeitando {
	some Barbero.afeita
} for 4

check elBarberoEsMujer {
	Barbero in Mujer and Barbero in Habitante - Hombre
} for 10

// Se puede asegurar que el barbero es mujer para que la paradoja se elimine.
