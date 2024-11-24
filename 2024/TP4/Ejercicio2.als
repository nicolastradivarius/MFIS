// Quiero realizar dinámica basada en relaciones para los marcadores de un unico libro.
open util/ordering[Tiempo] as ord

one sig Libro {
	paginas: some Pagina,
	// el libro tiene un conjunto de marcadores que cambia con el tiempo.
	// podrá tener cero, uno o más marcadores en un determinado timestamp.
	marcadores: set Marcador -> Tiempo
}

sig Marcador {
	// cambiamos a lone para permitir que un marcador no marque una página, y luego
	// sí la marque en un dado timestamp
	pag: lone Pagina
}

sig Pagina { }

sig Tiempo {}

// el libro puede tener entre cero y tres marcadores.
fact {all l: Libro | #l.marcadores >= 0}

fact {all l: Libro | #l.marcadores <= 3}

// el marcador no puede marcar una página que no esté en el conjunto de páginas del libro.
fact {no m: Marcador, l: Libro, t: Tiempo | (m in (l.marcadores).t) and ((m.pag) !in l.paginas) }

// da problemas
// un marcador que no esté en un libro en un determinado timestamp no puede marcar una página
fact {all m: Marcador, t: Tiempo, l: Libro | m not in (l.marcadores).t implies no m.pag}

fact {all p: Pagina | some l:Libro | p in l.paginas} -- no hay paginas sueltas

run default {}

---------------------------------------

/**
(c) Añada los predicados necesarios para modelar dinámica sobre los marcadores de un libro.
Los cambios de estado tendrán lugar por el agregado de un marcador,
la eliminación de un marcador y la modificación de la página marcada por un marcador del libro.
*/

// en el timestamp inicial, el libro no tiene marcadores
pred init [t: Tiempo, l: Libro] {
	no (l.marcadores).t
}

pred agregarMarcador [t1, t2: Tiempo, l: Libro, m: Marcador] {
	some p: Pagina | 
		(m not in (l.marcadores).t1) and
		(p in l.paginas) and
		(l.marcadores).t2 = (l.marcadores).t1 + m and
		(m.pag = p)
}

pred eliminarMarcador [t1, t2: Tiempo, l: Libro, m: Marcador] {

}

pred modificarMarcador [t1, t2: Tiempo, l: Libro, m: Marcador] {

}

pred hacerNada [t1, t2: Tiempo, l: Libro] {
	(l.marcadores).t1 = (l.marcadores).t2
}

fact traces {
	all l: Libro, t: Tiempo-ord/last | some m: Marcador |
		init[ord/first, l] and (
			agregarMarcador[t, t.next, l, m] or
			hacerNada[t, t.next, l]
		)
}

run default {some Marcador} for 5 Tiempo, exactly 3 Marcador, exactly 3 Pagina

run seAgregoMarcador {
	some m: Marcador, t: Tiempo, l: Libro | agregarMarcador[t, t.next, l, m]
} for 6 Tiempo, exactly 3 Marcador, exactly 3 Pagina


