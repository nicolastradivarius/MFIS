/*
“en una villa en la cual el barbero afeita a cada hombre que no se afeita a
 sí mismo, ¿quien afeita al barbero?”
*/

sig Hombre {
	afeita: set Hombre 
} 

sig Barbero extends Hombre {}

fact "los hombres que afeita el barbero son aquellos que no se afeitan a sí mismos" {
	Barbero.afeita = {h: Hombre | h !in h.afeita} 
}

fact "solo el barbero puede afeitar hombres" {
	all h: Hombre-Barbero | h.afeita = {h}
}

fact "hay muchos barberos" {
	some Barbero
}

---------------------------------------------------------------

run default {}

// notamos que en todas las instancias los barberos se afeitan a sí mismos.
check barberosSoloAfeitanBarberos {
	Barbero.afeita in Barbero
} for 12

// notamos que en todas las instancias hay ausencia de hombres que no se afeitan a sí mismos.
run algunosHombresQueNoSeAfeitan {
	#{h: Hombre-Barbero | h !in h.afeita} > 2
} for 12

run algunosHombresQueNoSeAfeitan2 {
	Barbero.afeita in Hombre-Barbero
} for 12

// Si bien el modelo actual permite solucionar la paradoja, lo hace de forma tal que los barberos
// sólo afeitan a otros barberos. Si consideramos que los hombres que no se afeitan a sí mismos
// pueden afeitar a otros hombres que tampoco se afeiten a sí mismos, entonces las soluciones
// serían válidas. Sin embargo, hay que recordar que no por nada había una distinción entre
// los barberos y los hombres que no se afeitaban a sí mismos: estos últimos no podían afeitar a nadie
