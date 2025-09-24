// TP3 2022, Ejercicio 1

sig Conjunto { 
	elementos: set Elemento 
}

sig Elemento {}

// todo conjunto cumple la siguiente condicion:
// existe otro conjunto y un elemento tal que:
// los elementos del primer conjunto son los mismos que los del otro agregandole el elemento
// el cual no pertenecia al primer conjunto.
/*
fact {
	all c1: Conjunto | some c2: Conjunto, e: Elemento |
		(c1.elementos = c2.elementos + e) and 
		(e ! in c1.elementos) 
}
*/

run default {}

/*
Problemas detectados:
- solo hay elementos, ningun conjunto. Esto ocurre porque el hecho que viene en el enunciado
restringe que todo conjunto c1 debe tener los mismos elementos que otro conjunto c2, 
agregando un elemento 'e' que no estaba en c1 previamente; pero si 'e' no estaba en c1, 
entonces no hay forma de respetar la igualdad, y ningun conjunto va a cumplir la condicion.
- hay elementos que no pertenecen a algun conjunto.
- hay dos atomos distintos de Conjunto que tienen los mismos elementos.
*/

fact "todo elemento esta en algun conjunto" {
	// la imagen de la relacion es Elemento.
	Conjunto.elementos = Elemento
}

run elementoSinConjunto {
	some e: Elemento | no c: Conjunto | e in c.elementos
} for 10

run conjuntoVacio {
	some c: Conjunto | no c.elementos
}

fact "si dos conjuntos poseen los mismos elementos, son el mismo conjunto" {
	// dicho de otra forma, si dos atomos son distintos, tienen distintos elementos
	all c1, c2: Conjunto |(c1.elementos = c2.elementos) implies c1 = c2
}

run dosConjuntosIguales {
	some disj c1, c2: Conjunto | 
		(c1.elementos in c2.elementos) and
		(c2.elementos in c1.elementos)
} for 7

// (b) Se puede asegurar que la cantidad maxima de elementos de un conjunto cualquiera
// equivale a la cantidad total de elementos que haya en una particular instancia.
check cantidadMaximaDeElementosDeUnConjunto {
	// la cantidad de elementos alcanzada por todos los elementos de todos los conjuntos de
	// la instancia equivale a la cantidad total de elementos.
	// esto es posible por el hecho que restringe que todo elemento esta en algun conjunto.
	#(Conjunto.elementos) = #Elemento
} for 10

fact todoConjuntoPuedeExpresarseComoLaUnionDeDosConjuntos {
// el problema que tiene esto es que al ser un cuantificador universal, tambien aplica para
// los "otros dos conjuntos". Es decir, si para c existe c1 y c2 tal que c = c1 U c2, tambien
// debe suceder que para c1 existan otros dos tal que su union sea c1... y para c2, y asi.
	all c: Conjunto | some disj c1, c2: Conjunto | 
		c.elementos = c1.elementos + c2.elementos
}
