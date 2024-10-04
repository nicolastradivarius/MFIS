/*
“en una villa en la cual el barbero afeita a cada hombre que no se afeita a
 sí mismo, ¿quien afeita al barbero?”
*/

abstract sig Habitante {
	afeita: set Hombre
}

sig Mujer extends Habitante {}

sig Hombre extends Habitante {}

one sig Barbero in Habitante {}
/*
fact "solo el barbero puede afeitar hombres" {
	all h: Habitante-Barbero | 
		// si el habitante se afeita a sí mismo, entonces sólo afeitará a sí mismo y no a otros.
		((h in h.afeita) implies #(h.afeita) = 1) and
		// si el habitante no se afeita a sí mismo, entonces no afeitará a otros.
		((h not in h.afeita) implies #(h.afeita) = 0)
	// nótese que la signatura Mujer no tiene la relación `afeita`, por lo que siempre caerá en
	// la segunda implicación y tiene sentido con que las mujeres no necesitan ser afeitadas
}
*/

// otra forma más simple de escribirlo es que para todos los habitantes excepto el barbero,
// el conjunto de habitantes que dicha persona afeita (exceptuándola a ella misma) es cero.
fact {
	all h: Habitante-Barbero | no (h.afeita - h)
}

fact "el barbero solo afeita a los hombres que no se afeitan a sí mismos" {
	Barbero.afeita = {h: Hombre | h !in h.afeita}
}
---------------------------------------------------------------

run default {some Hombre and some Mujer} for 4

// (a) Validación del modelo

check hombreQueSeAfeitaNoPuedeSerAfeitado {
	one b: Barbero | all h: Hombre | (h in h.afeita) implies (h !in b.afeita)
} for 6

check soloBarberoPuedeAfeitarOtrosHombres {
	all h: Habitante-Barbero | no (h.afeita - h)
} for 6

check elBarberoSiempreEsMujer {
	Barbero in Mujer
} for 12

run elBarberoPuedeSerHombre {
	Barbero in Hombre
}
----------------------------------------------------------------

// (b) El barbero tiene que ser mujer para que la paradoja se solucione. De esta manera, 
// el barbero no necesita afeitarse, al igual que las demás mujeres.
