/*
"En una villa donde el barbero afeita a cada hombre que no se afeita a si mismo,
quien afeita al barbero?"

La razon de que esto es una paradoja se debe a lo siguiente: 
- el pueblo tiene hombres y un unico barbero hombre.
- todos los hombres necesitan afeitarse.
- si un hombre puede afeitarse a si mismo, no necesita del barbero.
- si un hombre no puede afeitarse a si mismo, solo el barbero puede afeitarlo, y no otro hombre.
- el barbero es un hombre, y por ende, necesita afeitarse. He aqui la paradoja:
	- si el barbero se afeita a si mismo, entonces el barbero estaria afeitando a un hombre
	que se afeita a si mismo (ese hombre es el barbero mismo), contradiciendo lo dicho.
	- si el barbero no se afeita a si mismo, entonces necesita de un barbero que lo afeite,
	pero no hay otros barberos en el pueblo ademas de el, por lo que es imposible.
Esta paradoja surge de que los conjuntos pueden ser miembros de si mismos.
https://es.wikipedia.org/wiki/Paradoja_de_Russell
En este caso, al barbero ser un hombre, esta incluido en las condiciones para afeitarse.
Esto se solucionaria si se considera al barbero como una especie independiente al hombre,
o en su defecto, como una mujer (inciso b). Tambien podria haber multiples barberos hombres.
*/

sig Hombre { 
	afeita: set Hombre 
}

one sig Barbero extends Hombre {}

// este hecho establece que el barbero afeita a todos los hombres que se afeitan a si mismos.
fact {
//	Barbero.afeita = {h: Hombre | h in h.afeita} 
// 	Corregido:
	Barbero.afeita = {h: Hombre | h not in h.afeita} 
}

fact "los hombres que no sean el barbero no pueden afeitar a otros hombres" {
	all h: Hombre - Barbero | no h2: Hombre - {h} | h2 in h.afeita
}

run default {}

run hombreAfeitandose {
	some h: Hombre - Barbero | h in h.afeita
}

run hombreAfeitandoAOtros {
	some disj h1, h2: Hombre - Barbero | h2 in h1.afeita
}


/*
Problemas detectados (ignorando que el hecho de arriba es incorrecto):
- el barbero afeita hombres que ya se afeitaban a si mismos;
- hay hombres mas alla del barbero que afeitan a otros hombres;
- el barbero se afeita a si mismo.

Solucionados estos problemas, no se encuentran instancias para el modelo.
*/
