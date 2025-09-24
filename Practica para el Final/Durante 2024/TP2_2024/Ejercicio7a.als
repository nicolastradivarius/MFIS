/**
en una villa en la cual el barbero afeita a cada hombre que no se afeita
a sí mismo, ¿quién afeita al barbero?
*/

sig Hombre { 
	afeita: set Hombre 
} 

one sig Barbero extends Hombre {} 

/*
fact { 
	// el conjunto de hombres que afeita el barbero son todos aquellos que
	// se afeitan a sí mismos.
	// Esto es incorrecto y debería ser corregido con un !in.
	// Además se debe excluir al barbero de la cuantificación porque sino,
	// se estaría requiriendo que el barbero se afeite a sí mismo.
	Barbero.afeita = {h: Hombre | h in h.afeita} 
}
*/

run default {} for 4

/*
Las instancias muestran situaciones en las que:
- el barbero afeita a hombres que ya se afeitan a sí mismos
- hay hombres que afeitan al barbero
- el barbero se afeita a sí mismo
- el barbero no afeita a nadie
- hay hombres que quedan sin afeitar
- hay hombres que afeitan a otros hombres
*/



/* 
Si excluyo al barbero de la cuantificación, estoy diciendo que
el barbero no se afeita a sí mismo, pero eso lo convertiría en
un hombre que no se afeita a sí mismo y por ende tendría que 
ser afeitado por el barbero, que es él mismo, haciendo que
se afeite a sí mismo.
Si en cambio permito que forme parte de la cuantificación, 
el barbero se afeitaría a sí mismo, pero eso lo convertiría en
un hombre que se afeita a sí mismo y por ende no tendría que
ser afeitado por un barbero, el cual es él mismo.
La idea es que Alloy trabaje para decidir cómo debe ser la 
solución si el barbero se afeita o no a sí mismo. Al excluirlo
de la cuantificación estoy forzando una situación, por lo que
debo permitir que el barbero se pueda afeitar o no a sí mismo, a 
ver qué pasa.
*/
fact "el barbero afeita a hombres que no se afeitan a sí mismos" {
//	Barbero.afeita = {h: Hombre-Barbero | h !in h.afeita}
	Barbero.afeita = {h: Hombre | h !in h.afeita}
}

fact "solo el barbero afeita a otros hombres" {
	all h: Hombre-Barbero | 
		((h in h.afeita) implies (one h.afeita)) and
		((h !in h.afeita) implies (no h.afeita))
}

// Solución a la paradoja: no existe.
run afeitadorDeBarbero {
	some h: Hombre | Barbero in h.afeita
} for 9

run hombresQueAfeitanOtrosHombres {
	some disj h1, h2: Hombre-Barbero | h2 in h1.afeita
}

// Siempre elige al Barbero. Si lo excluimos de la cuantificación,
// no hay instancias.
run hombresSinAfeitar {
	some h: Hombre | h !in Hombre.afeita
}
