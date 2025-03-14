abstract sig Person { 
	children: set Person,
	siblings: set Person
}

sig Man, Woman extends Person {}

sig Married in Person { 
	spouse: one Married
}

run default {} for 5

/*
Problemas detectados:

- existen hombres y mujeres casados consigo mismos,
- existen hombres y mujeres que son primos de sí mismos,
- existe una mujer que tiene un hijo, está casada con un hombre y dicho hombre es primo de ese hijo,
- el hijo anteriormente mencionado es a la vez primo de su madre,
- hombres y mujeres son hijos, primos y están casados entre sí al mismo tiempo,
- hombres y mujeres con más de un padre o madre

*/

fact "ninguna persona puede ser su propio ancestro (la relación children no es reflexivo-transitiva)" {
	no p: Person | p->p in ^children
}

fact "ninguna persona puede ser su propio primo (la relación siblings no es reflexiva)" {
	no p: Person | p->p in siblings
}

fact "ninguna persona puede estar casada con sí misma (la relación spouse no es reflexiva)" {
	no p: Married| p->p in spouse
}

fact "una persona no puede estar casada con un ancestro" {
	all disj p1, p2: Married | esAncestro[p1, p2] implies not estaCasado[p1, p2]
}

fact "una persona no puede estar casada con un primo" {
	all disj p1, p2: Married | sonPrimos[p1, p2] implies not estaCasado[p1, p2]
}

fact "una persona que está casada con alguien no puede estar casada con otra persona" {
	// o sea, la relacion es biyectiva. 
	// o sea, la cantidad de personas con la que puede estar casada es 1.
	all p: Married | (one spouse.p)
}

fact "no existen parejas casadas de forma unidireccional (la relación spouse es simétrica)" {
	all p1, p2: Married | (p1->p2) in spouse implies ~(p1->p2) in spouse
}

fact "no existen primos de forma unidireccional (la relación siblings es simétrica)" {
	all p1, p2: Person | (p1->p2) in siblings implies ~(p1->p2) in siblings
}

fact "ninguna persona puede tener mas de una madre ni mas de un padre" {
	all p: Person | (lone padre[p]) and (lone madre[p])
}

fact "los hijos de una persona casada son los mismos que su pareja" {
	all disj p1, p2: Married | 
		estaCasado[p1, p2] implies (p1.children = p2.children)
}

fact "no pueden ser primos quienes tienen una relación de descendencia" {
	all disj p1, p2: Person | (p1->p2 in siblings) implies (not esAncestro[p1, p2])
}

fact "una persona no puede tener hijos con un familiar" {
	//all p: Person | no (p.children) & (p.siblings.children)
}

fact "una persona no puede tener de hijos a los hijos de sus descendientes" {
	
}

fact "los hijos de una persona no pueden ser primos entre sí" {
	
}


-------------------- PREDICADOS Y FUNCIONES -----------------------



pred estaCasado[p1, p2: Married] {
	(p1 = p2.spouse) and (p2 = p1.spouse)
}

pred sonPrimos[p1, p2: Person] {
	(p1 in p2.siblings) and (p2 in p1.siblings)
}

// predicado para determinar si p1 y p2 son padres de p0
pred sonPadres[p1, p2, p0: Person] {
	// caso 1: p1 es el padre y p2 es la madre
	(p1 = padre[p0] and p2 = madre[p0]) or
	// caso 2: al revés del 1
	(p2 = padre[p0] and p1 = madre[p0])
}

pred esHijo[p1, p2: Person] {
	p1 in p2.children
}

pred esTio[p1, p2: Person] {
	// p1 es tío de p2 si p2 es primo de alguno de los hijos de p1
	some (p2.siblings & p1.children)
}

pred esAncestro[p1, p2: Person] {
	// p1 es ancestro de p2 si es posible encontrar una tupla (p1, p2) en la relación ^children
	(p1->p2) in ^children
}

pred esDescendiente[p1, p2: Person] {
	~(p1->p2) in ^children
}

// funciones para obtener el padre y madre de una dada persona.
fun padre [p: Person]: one Man {
	children.p & Man
}

fun madre [p: Person]: one Woman {
	children.p & Woman
}

fun padres[p: Person]: set Person {
	padre[p] + madre[p]
}

fun primos[p: Person]: set Person {
	p.siblings
}

fun ancestros[p: Person]: set Person {
	^children.p
}

fun descendientes[p: Person]: set Person {
	p.^children
}

/*
fun ancestros[p: Person]: set Person { 
	// corroborar
//	{p2: Person | p2 in ^children.p
}
*/

// función para obtener los hermanos (y medio-hermanos) de una persona.
// los medio-hermanos son aquellos que comparten algún ancestro en común con p.
fun hermanos[p: Person]: set Person {
	// los hermanos directos de una persona
	{p2: Person | p2 in (padres[p].children - p)}
}


--------------------------- COMANDOS DE VALIDACIÓN ---------------------------


// busca instancias donde haya una relacion de hijo entre tres personas, i.e, el abuelo es hijo
// de su nieto.
run tresAncestrosCirculares {
	some disj p1, p2, p3: Person |
		(p1 in p2.children) and (p2 in p3.children) and (p3 in p1.children)
} for 5

// busca instancias donde X esté casado con Y, pero Y no esté casado con X.
run casadoPeroNoCasado {
	some disj p1, p2: Married | 
		(p1 in p2.spouse) and (p2 not in p1.spouse)
} for 5

check hijosDeHombreSonLosMismosQueSuMujer {
	all disj m: Married & Man, w: Married & Woman |
		((w = m.spouse and some m.children) implies (m.children = w.children)) and
		((m = w.spouse and some w.children) implies (w.children = m.children))
} for 6

run esAncestroCasoExito {
	some disj p1, p2: Person | esAncestro[p1, p2]
} for 6

run personaCasadaConPrimos {
	some disj p1, p2: Married | p1.spouse = p2 and p1 in p2.siblings
} for 10



run padreHijo {some disj p1, p2: Person | (padre[p2] = p1)}

run dosPadres {one p: Person | (#padre[p] = 3)} for 10

run padreHijoHijo {
	some disj p1, p2, p3: Person | (p2 in p1.children) and (p3 in p2.children)
}


//los hermanos de una persona son aquellas personas que poseen algun ancestro en comun

