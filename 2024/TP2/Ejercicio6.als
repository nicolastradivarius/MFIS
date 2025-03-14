/*
En matematicas, un conjunto es una colección de elementos considerada en sí misma como un
objeto. Los elementos de un conjunto pueden ser, por ejemplo, personas, números, colores, letras, 
figuras, etc. Se dice que un elemento (o miembro) pertenece a un conjunto si está incluido de algún 
modo dentro de él. Si dos conjuntos poseen los mismos elementos, entonces son el mismo conjunto. 
El conjunto que no contiene elementos se llama conjunto vacío, denotado como ∅ o {}, y claramente 
es un conjunto.
El siguiente modelo intenta capturar la noción básica de conjunto:
*/

sig Conjunto {
	// cambio la multiplicidad a `set` para permitir la existencia de ∅
	elementos: set Elemento 
}

sig Elemento {}

// comento el fact para evitar la no existencia de conjuntos.
/*
fact  { 
	all c1: Conjunto | 
		some c2: Conjunto, e: Elemento | 
			(c1.elementos = c2.elementos + e) and 
			(e ! in c1.elementos) 
}
*/

/*
(a) Utilice el analizador para validar si el modelo es correcto. Indique cuáles son los problemas del 
modelo, corríjalos, y valide el modelo nuevamente. En todos los casos, explique el resultado 
brindado por el Analizador en respuesta a la ejecución de los comandos definidos para realizar 
la validación.
*/

run default {} for 6 but 6 Int

run hayConjuntos {#Conjunto > 1} for 6

/*
En todas las instancias hay ausencia de átomos de Conjunto.
Veamoslo con el siguiente ejemplo:
	- Conjunto = {C1, C2}
	- Elemento = {E0, E1}
Se debe cumplir las siguientes condiciones en la misma instancia:
	- para C1 existe al menos un conjunto y un elemento `e` tal que C1 contiene a ese
	conjunto pero difiere en ese elemento `e`. Ese nuevo conjunto no puede ser C1 mismo ya que
	C1 nunca podría diferir en un elemento consigo mismo. Entonces C2 es el conjunto, y 
	así (C1.elementos = C2.elementos + e) y (e !in C1.elementos), lo cual se valida si
	C1.elementos = {E0, E1} y C2.elementos = {E0} siendo `e` = E1. Hasta acá todo bien.
	- para C2 existe al menos un conjunto y un elemento `e` tal que C2 contiene a ese
	conjunto pero difiere en `e`. La única posibilidad es que C1 sea ese conjunto, de manera que
	(C2.elementos = C1.elementos + e) y (e !in C2.elementos). Pero para que esto ocurra, C2 debe
	contener a C1, y dada la instancia donde se satisface la condición de arriba, esto nunca va a 
	suceder.
Por lo tanto es imposible que exista una instancia donde ambas condiciones se satisfagan.
Para evitar esta situación, comentamos el fact original del modelo.
*/

fact "dos conjuntos con los mismos elementos son el mismo conjunto" {
	no disj c1, c2: Conjunto | (c1.elementos = c2.elementos)
}


fact "todo elemento está en algún conjunto" {
	Elemento in Conjunto.elementos
}

run conjuntoVacio {
	some c: Conjunto | no c.elementos
}

check conjuntosDiferentesElementosDiferentes {
	no c1, c2: Conjunto | (c1 != c2) and (c1.elementos = c2.elementos)
} for 12

run conjuntoIncluido {
	some disj c1, c2: Conjunto | (c1.elementos in c2.elementos)
}

run conjuntoNoVacioIncluido {
	some disj c1, c2: Conjunto | (some c1.elementos) and (c1.elementos in c2.elementos)
}

run conjuntoVacioIncluido {
	some disj c1, c2: Conjunto | 
		(no c1.elementos) and 
		(c1.elementos in c2.elementos)
}

// no encuentra instancias por la keyword disj: si ambos no tienen elementos, deben ser el mismo.
run conjuntoVacioIncluidoVacio {
	some disj c1, c2: Conjunto | 
		(no c1.elementos) and 
		(no c2.elementos) and
		(c1.elementos in c2.elementos)
}

run conjuntoVacioIncluidoVacio2 {
	some c1, c2: Conjunto | 
		(no c1.elementos) and 
		(no c2.elementos) and
		(c1.elementos in c2.elementos)
}

run conjuntoNoVacioIncluidoVacio {
	some disj c1, c2: Conjunto | 
		(some c1.elementos) and 
		(no c2.elementos) and
		(c1.elementos in c2.elementos)
}