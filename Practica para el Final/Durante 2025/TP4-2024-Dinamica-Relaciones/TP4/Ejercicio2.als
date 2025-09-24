open util/ordering[Libro]

sig Libro { 
	paginas: some Pagina,
	marcadores: set Marcador 
}

sig Marcador {
	pag: set Pagina 
}

sig Pagina { }

// el maximo de marcadores que puede tener el libro es tres.
fact {all l: Libro | #l.marcadores <= 3}

/*
Por que impide la generacion de instancias? 
fact {
	all m: Marcador, l: Libro |
		m.pag in l.paginas iff m in l.marcadores
}

Lo mismo con este otro
// no hay un marcador que no este en el libro y marque una pagina del libro
fact {
	no m: Marcador, l: Libro | (m not in l.marcadores) and (m.pag in l.paginas)
}

Lo mismo con este otro
fact {
	all m: Marcador, l: Libro | (m not in l.marcadores) implies (no m.pag)
}
*/

// no hay un marcador que este en el libro y marque una pagina que no lo esta.
fact {no m: Marcador, l: Libro | (m in l.marcadores) and (m.pag !in l.paginas) }




fact init {
	// inicialmente el libro no tiene marcadores
	first.marcadores = none
}

fact estadosValidos {
	// todo estado (libro) tiene que cumplir que
	all lib: Libro - last |
		// no hay cambios en las paginas del libro
		preservaPaginas[lib, lib.next]
}

pred preservaPaginas [lib1, lib2: Libro] {
	lib1.paginas = lib2.paginas
}

run default {}

run libroConTresPaginas {
	#Libro.paginas = 3 and some Libro.marcadores
} for 6

run libroConTresMarcadores {
	#Libro.marcadores = 3 and #Libro.paginas = 3
}

// Caso donde hay un marcador que no esta en el libro pero marca una pagina que si lo esta
run marcadorMarcaPaginaInexistente {
	some m: Marcador, l: Libro | (m not in l.marcadores) and (m.pag in l.paginas)
}

fact traces {
	all lib: Libro - last |
		agregarMarcador[lib, lib.next] or
		eliminarMarcador[lib, lib.next]
}

------------------------

pred agregarMarcador[l1, l2: Libro] {
	some m: Marcador |
		m not in l1.marcadores and 
		l2.marcadores = l1.marcadores + m and
		some p: l1.paginas | m.pag = p
}

pred eliminarMarcador[l1, l2: Libro] {
	some m: Marcador |
		m in l1.marcadores and
		l2.marcadores = l1.marcadores - m
}

pred modificarPaginaMarcada[l1, l2: Libro, m: Marcador] {
	m in l1.marcadores and
	m in l2.marcadores 
	
}

run eliminarMarcador
