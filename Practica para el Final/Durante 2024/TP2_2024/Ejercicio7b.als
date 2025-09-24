/**
en una villa en la cual el barbero afeita a cada hombre que no se afeita
a sí mismo, ¿quién afeita al barbero?
*/

abstract sig Persona {
	afeita: set Hombre 
}

sig Hombre, Mujer extends Persona {}

one sig Barbero in Persona {} 

run default {} for 6

fact "la villa tiene hombres y mujeres" {
	some Hombre and some Mujer
}

fact "el barbero afeita a cada hombre que no se afeita a sí mismo" {
	Barbero.afeita = {h: Hombre | h !in h.afeita}
}

fact "solo el barbero afeita a otros hombres" {
	all h: Persona-Barbero | 
		(h in h.afeita implies one h.afeita) and
		(h !in h.afeita implies no h.afeita)
}

// No encuentra instancias. Nadie afeita al barbero
run afeitadorDeBarbero {
	some p: Persona | Barbero in p.afeita
} for 8


// No encuentra contraejemplos. El barbero es mujer.
// Por eso nadie afeita al barbero.
check barberoEsMujer {
	Barbero in Mujer
} for 12


/**
Finalmente se llega a la conclusión de que, al permitir la
existencia de mujeres en la villa, el barbero tiene que ser mujer.
*/
