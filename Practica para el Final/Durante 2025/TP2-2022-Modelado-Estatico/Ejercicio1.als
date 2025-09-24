// Juan y Pedro son signaturas singleton (solo tienen un atomo)
one sig Juan, Pedro {}

// Culpable es una signatura contenida en todo el universo de Alloy, esto es, puede contener
// cualquier atomo, desde atomos de otras signaturas como numeros enteros.
sig Culpable in univ {}

// Juan no pertenece al conjunto Culpable
//fact { Juan not in Culpable }

// Si Juan esta en el conjunto Culpable entonces Pedro tambien
fact { Juan in Culpable implies Pedro in Culpable }

// Se cree que Pedro no esta en el conjunto Culpable.
assert conclusion { Pedro not in Culpable }

run default {}

/*
El modelo consiste de que Pedro puede o no ser culpable. Juan no es culpable.
Asimismo, los numeros enteros del modelo (determinados por el bitwidth) tambien pueden
ser culpables o no.
*/

// Se chequea la asercion y devuelve contraejemplos en los que Pedro es culpable.
check conclusion
// Esto sucede porque la restriccion esta puesta sobre Juan, no sobre Pedro.
// Es decir, la implicacion se hace verdadera tanto si Juan es culpable como si no.
// Como se restringio que Juan no es culpable, entonces el antecedente siempre es falso,
// y la implicacion se satisface siempre, independientemente de si Pedro es o no culpable.

run {some Juan & Culpable}
run {no Pedro & Culpable}
run {no Juan & Culpable and some Pedro & Culpable} for 6
run {no (Juan+Pedro) & Culpable} for 6

// Si se elimina el primer hecho (Juan no es culpable), ahora Juan puede pertenecer al
// conjunto Culpable, haciendo que, o ambos son culpables, o ambos no lo son, o solo Pedro.


