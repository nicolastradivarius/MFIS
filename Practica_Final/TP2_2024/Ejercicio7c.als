/**
en una villa en la cual el barbero afeita a cada hombre que no se afeita
a sí mismo, ¿quién afeita al barbero?
*/

sig Hombre { 
	afeita: set Hombre 
} 

some sig Barbero extends Hombre {}

run default {} for 4


fact "el barbero afeita a hombres que no se afeitan a sí mismos" {
	Barbero.afeita = {h: Hombre | h !in h.afeita}
}

fact "solo el barbero afeita a otros hombres" {
	all h: Hombre-Barbero | 
		((h in h.afeita) implies (one h.afeita)) and
		((h !in h.afeita) implies (no h.afeita))
}


// todos los barberos son afeitados por alguien.
check barberosAfeitados {
	all b: Barbero | some b2: Barbero | b in b2.afeita
} for 18

run hombresQueAfeitanOtrosHombres {
	some disj h1, h2: Hombre-Barbero | h2 in h1.afeita
}


run hombresSinAfeitar {
	some h: Hombre | h !in Hombre.afeita
}

/**
Al permitir la existencia de más de un barbero, sucede que
en todas las instancias, hay una cadena de afeitamiento
de barberos, es decir, un ciclo en el que los barberos
se afeitan los unos a los otros.
*/
