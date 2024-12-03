// Quiero realizar dinámica basada en relaciones para los marcadores de un unico libro.
open util/ordering[Estado] as ord

one sig Libro {
	paginas: some Pagina,
}

sig Marcador {}

sig Pagina {}

sig Estado {
	// como tenemos un unico libro, podemos prescindir de él en la relación.
	// si tuviéramos varios libros, hay que hacer "marcadores: Libro -> set Marcador" como en el caso de los semáforos.
	marcadores: Marcador -> one Pagina
}


// el libro puede tener entre cero y tres marcadores.
fact estado_valido {
	all e: Estado | #(e.marcadores).Pagina >= 0 and #(e.marcadores).Pagina <= 3
}
/*
// el marcador no puede marcar una página que no esté en el conjunto de páginas del libro.
// Es decir, no puede ocurrir al mismo tiempo que un marcador esté en el conjunto de marcadores del libro
// y que la página que marque no esté en el libro.
fact {no m: Marcador, e: Estado | (m in (e.marcadores)) and ((m.marca) !in Libro.paginas) }

// un marcador que no esté en un libro en un determinado estado no puede marcar una página.
fact {all m: Marcador, e: Estado | m not in (e.marcadores) implies no m.marca}

fact {all p: Pagina | some l:Libro | p in l.paginas} -- no hay paginas sueltas
*/

---------------------------------------

/**
(c) Añada los predicados necesarios para modelar dinámica sobre los marcadores de un libro.
Los cambios de estado tendrán lugar por el agregado de un marcador,
la eliminación de un marcador y la modificación de la página marcada por un marcador del libro.
*/

// en el estado inicial, el libro no tiene marcadores
pred init [e: Estado] {
	no (e.marcadores)
}

pred agregarMarcador [e1, e2: Estado] {
/*	some m: Marcador, p: Libro.paginas | 
		m !in e1.marcadores and
		e2.marcadores = e1.marcadores + m */
}

pred eliminarMarcador [e1, e2: Estado] {

}

pred modificarMarcador [e1, e2: Estado] {

}

pred hacerNada [e1, e2: Estado] {
	e1.marcadores = e2.marcadores
}

fact traces {
	all e1: Estado - ord/last | let e2 = e1.next |
		init[ord/first] and
		(
			agregarMarcador[e1, e2] or

			hacerNada[e1, e2]
		)
}

run default {some marcadores} for 9 

run seAgregoMarcadorDosVeces {
	some disj e1, e3: Estado-ord/last | let e2 = e1.next | let e4 = e3.next | 
		agregarMarcador[e1, e2] and
		agregarMarcador[e3, e4]
}  for 9


