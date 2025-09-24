sig Conjunto { 
	elementos: set Elemento 
} 

sig Elemento {}


fact "todo elemento pertenece a algún conjunto" {
	all e: Elemento | some elementos.e
}


fact "dos conjuntos con los mismos elementos son el mismo conjunto" {
	all c1, c2: Conjunto | 
		(c1.elementos = c2.elementos) implies (c1 = c2)
}

run default {} 

assert cantidadMaximaDeElementosDeLosConjuntos {
	// La cantidad de elementos de los conjuntos es igual a la
	// cantidad total de elementos existentes en la instancia.
	#(Conjunto.elementos) = #Elemento
}


check cantidadMaximaDeElementosDeLosConjuntos for 8
