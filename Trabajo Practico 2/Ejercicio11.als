abstract sig Person { 
	children: set Person,
	siblings: set Person
}

sig Man, Woman extends Person {}

sig Married in Person { 
	spouse: one Married
}

/*
Acerca de la multiplicidad en el tipo de retorno:
The constraints implicit in the declarations of arguments of functions
and predicates are conjoined to the body constraint when a function
or predicate is run. When a function or predicate is invoked (that is,
used within another function or predicate but not run directly), 
these implicit constraints are ignored. You should therefore not
rely on such declaration constraints to have a semantic effect; they are
intended as redundant documentation. A future version of Alloy may
include a checking scheme that determines whether actual expressions
have values compatible with the declaration constraints of formals.
Referencia: https://alloytools.org/download/alloy-language-reference.pdf
Página 268-269
Si bien no menciona la multiplicidad del retorno, sino restricciones sobre
los argumentos, en base a esto y a algunas pruebas, 
se podría suponer que colocar multiplicidad en el retorno
no tiene ningún efecto sobre el mismo.
*/
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
