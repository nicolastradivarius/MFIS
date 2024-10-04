
/*
Genere y analice tres instancias del modelo brindado. ¿Qué irregularidades detecta? Especifique
comandos en Alloy que incluyan las restricciones necesarias para generar instancias que ilustren 
explícitamente cada irregularidad.

Respuesta: 
*/

abstract sig Person { 
    children: set Person,
    siblings: set Person
}

sig Man, Woman extends Person {}

sig Married in Person { 
    spouse: one Married
}

fun padre [p: Person]: Man {
    children.p & Man
}

fun madre [p: Person]: Woman {
    children.p & Woman
}

run padreHijo {some disj p1, p2: Person | (padre[p2] = p1)}
run dosPadres {one p: Person | (#padre[p] = 3)}

// ninguna persona puede ser su propio ancestro
check noSelfAncestor {
    no p: Person | p in p.^children
} for 10

// una persona puede tener como máximo dos padres
check atMostTwoParents {
    all p: Person | #padre[p] <= 2 and #madre[p] <= 2
} for 10

// una persona casada tiene exactamente un cónyuge
check oneSpouse {
    all m: Married | one m.spouse
} for 10comandos en Alloy que incluyan las restricciones necesarias para generar instancias que ilustren 
expl´ıcitamente cada irregularidad.

Respuesta: 
*/

abstract sig Person { 
	children: set Person,
	siblings: set Person
}

sig Man, Woman extends Person {}

sig Married in Person { 
	spouse: one Married
}

fun padre [p: Person]: Man {
	children.p & Man
}

fun madre [p: Person]: Woman {
	children.p & Woman
}

run padreHijo {some disj p1, p2: Person | (padre[p2] = p1)}
run dosPadres {one p: Person | (#padre[p] = 3)}

//ninguna persona puede ser su propio ancestro
fact {all p: Person | (p not in padre[p]) and (p not in madre[p])}

//ninguna persona puede tener mas de una madre ni mas de un padre
fact {all p: Person | (lone padre[p]) and (lone madre[p])}

//los hermanos de una persona son aquellas personas que poseen algun ancestro en comun
fun hermanos [p: Person]: Person {
	{pp: Person | (pp != p) and ((padre[p] = padre[pp]) or (madre[p] = madre[pp]))}
}

run personaTresHijos {some p: Person | #(p.children) = 3} for 7

run hermanosDeUnaPersona {some p: Person | some hermanos[p]}

assert hijosDeHombreSonLosMismosQueSuMujer {
	all m: Man | one w: Woman | (some m.children) implies (m.children = w.children)
}

check hijosDeHombreSonLosMismosQueSuMujer for 6

run {} for 6
