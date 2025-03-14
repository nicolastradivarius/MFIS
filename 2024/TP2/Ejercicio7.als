/*
“en una villa en la cual el barbero afeita a cada hombre que no se afeita a
 sí mismo, ¿quien afeita al barbero?”
*/

sig Hombre {
	afeita: set Hombre 
} 

one sig Barbero extends Hombre {}

/*
Con este fact, el barbero puede afeitar a hombres que se afeitan a sí mismos, lo cual no es valido
fact {
	Barbero.afeita = {h: Hombre | h in h.afeita} 
}
*/

// Con este fact, ahora Alloy no genera instancias. 
// El modelo es inconsistente debido a la paradoja inherente de "¿quién afeita al barbero?".
// Esta inconsistencia lleva a que Alloy no pueda generar ninguna instancia válida.
fact "los hombres que afeita el barbero son aquellos que no se afeitan a sí mismos" {
	Barbero.afeita = {h: Hombre | h !in h.afeita} 
}

fact "solo el barbero puede afeitar hombres" {
	all h: Hombre-Barbero | h.afeita = {h}
}

---------------------------------------------------------------

run default {} for 6

// (a) Validación del modelo

check hombreQueSeAfeitaNoPuedeSerAfeitado {
	one b: Barbero | all h: Hombre | (h in h.afeita) implies (h !in b.afeita)
} for 6

// falla, o sea que hay hombres (que no son barberos) que afeitan a otros hombres.
check soloBarberoPuedeAfeitarOtrosHombres {
	all h: Hombre | (h != Barbero) implies (no h.afeita)
} for 4

/*
Debido a que estamos ante una situación paradójica, no es posible encontrar
 instancias del modelo que muestren la situación.
*/
