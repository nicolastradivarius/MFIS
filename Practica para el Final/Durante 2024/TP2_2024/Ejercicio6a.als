sig Conjunto { 
	elementos: set Elemento 
} 

sig Elemento {}


// Este hecho exige que siempre haya un conjunto adicional (c2) que
// contenga un elemento más (e) que c1. Como no se especifica disj,
// c2 podría ser c1, pero eso nunca haría satisfacer el hecho dado
// que tiene que tener un elemento más que c1.
// Para un scope de tres, si c1 tiene un elemento, tiene que haber
// un c2 que tenga dos (de los cuales uno puede ser el mismo que
// tiene c1), y otro c3 que tenga tres (dos pueden ser los de c2), 
// habiendo alcanzado el máximo de tres conjuntos y tres elementos
// pero el conjunto c3 tiene que satisfacer el hecho, y no existe
// otro conjunto c4 que tenga un elemento más que c3. Por eso, 
// cualquiera sea la cantidad de conjuntos, este hecho nunca
// se podrá satisfacer a menos que no haya conjunto alguno (como
// sucede en todas las instancias).

/*
fact { 
	all c1: Conjunto | 
		some c2: Conjunto, e: Elemento | 
			(c1.elementos = c2.elementos + e) and 
			(e ! in c1.elementos) 
}
*/

run default {}

// No encuentra instancias. hay algún problema que evita
// la existencia de átomos de Conjunto.
run algunConjunto { some Conjunto }

// Encuentra instancias. No deberían existir elementos que no
// pertenezcan a algún conjunto.
run elementoSinConjunto {
	some e: Elemento | no elementos.e
}

fact "todo elemento pertenece a algún conjunto" {
	all e: Elemento | some elementos.e
}

// Encuentra instancias. No deberían existir átomos distintos
// de Conjunto que tengan los mismos elementos, porque
// deberían ser el mismo átomo.
run dosConjuntosConMismosElementos {
	some disj c1, c2: Conjunto | c1.elementos = c2.elementos
} for 9

fact "dos conjuntos con los mismos elementos son el mismo conjunto" {
	all c1, c2: Conjunto | 
		(c1.elementos = c2.elementos) implies (c1 = c2)
}
