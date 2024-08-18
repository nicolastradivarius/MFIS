sig Biblioteca {
	coleccion: set Libro
}

sig Libro {
	escritoPor: set Autor,
	genero: one GeneroLiterario
}

sig Autor {}

sig Novelista, Poeta, Periodista extends Autor {}

abstract sig GeneroLiterario {}

one sig Epico, Lirico, Dramatico extends GeneroLiterario {}

fact "no hay generos literarios que no tengan libros representativos" {
	no g: GeneroLiterario | no genero.g 
}

fact "no hay autores que no hayan escrito ningún libro" {
	all a: Autor | some escritoPor.a
}

fact "novelistas y poetas no son autores de los mismos libros" {
	escritoPor.Novelista & escritoPor.Poeta = none
}


/*
fact "novelistas y poetas no son autores de los mismos libros" {
	all l: Libro | 
		no a1, a2: Autor |
			(a1 in Novelista) and
			(a2 in Poeta) and
			(a1 in l.escritoPor) and
			(a2 in l.escritoPor)
}

// alternativa 2
fact "novelistas y poetas no son autores de los mismos libros" {
	all l: Libro | 
		no a1, a2: Autor |
			(a1 in Novelista) and
			(a2 in Poeta) and
			(a1 in autores[l]) and
			(a2 in autores[l])
}

// alternativa 3
fact "novelistas y poetas no son autores de los mismos libros" {
	all l: Libro | 
		no a1, a2: Autor |
			(a1 in autores_clase[l, Novelista]) and
			(a2 in autores_clase[l, Poeta])
}

// alternativa 4
fact "novelistas y poetas no son autores de los mismos libros" {
	all l: Libro | 
		no a1, a2: Autor |
			(a1 in autores_novelistas[l]) and
			(a2 in autores_poetas[l])
}
*/

fun autores [l: Libro]: set Autor {
	l.escritoPor
}

fun autores_novelistas [l: Libro]: set Novelista {
	autores[l] & Novelista
}

fun autores_poetas [l: Libro]: set Poeta {
	autores[l] & Poeta
}

fun autores_periodistas [l: Libro]: set Periodista {
	autores[l] & Periodista
}

fun autores_clase [l: Libro, clase: set Autor]: set Autor {
	autores[l] & clase
}

assert autores_equivale_autores_clase {
	all l: Libro | autores[l] = autores_clase[l, Autor]
}

check autores_equivale_autores_clase for 8

run default {}

run libro_con_al_menos_tres_autores {
	some l: Libro | #autores[l] >= 3
}

// definimos un conjunto por comprensión con las llaves de adentro.
run mas_de_un_libro_con_al_menos_dos_autores_novelistas {
	#{l: Libro | #autores_novelistas[l] >= 2} > 1
}

---- Modelado de comportamiento dinámico: AGREGAR ----

// definimos un predicado que permita modelar el agregado de un libro nuevo a la biblioteca
// (método del nuevo átomo). No consideramos restricciones.
// versión 1: se hace True sólo cuando efectivamente se agrega el libro a la biblioteca.
// versión 2: se hace True siempre (se agregue el Libro o no).
pred agregar_v1 [l: Libro, bi, bf: Biblioteca] {
	// precondiciones: el libro `l` no estaba previamente en la biblioteca.
	(l not in bi.coleccion)

	// postcondiciones: la biblioteca final `bf` tiene los libros de `bi` sumado el libro `l`.
	(bf.coleccion = bi.coleccion + l)
}

pred agregar_v2 [l: Libro, bi, bf: Biblioteca] {
	// no hay precondiciones.
	(bf.coleccion = bi.coleccion + l)
}

// buscamos instancias con restricciones que hagan que los predicados de dinámica se cumplan.
// si en lugar de eso vamos explorando las instancias por default, nos encontraremos muchas
// donde los predicados no se cumplen (lo vemos usando el analizador). Casos de estos son aquellos
// donde hay sólo un átomo de Biblioteca e intentamos ver si se cumple agregar_v1: la única manera
// de que se cumpla ese predicado es habiendo dos átomos de Biblioteca, ya que en uno, el libro `l`
// no está en su colección, y en el otro debe estarlo, lo cual es imposible de conseguir usando
// la primer versión (pero sí es posible conseguir con la segunda versión).

run agregar_v1_caso_exito {
	some l: Libro, bi, bf: Biblioteca | agregar_v1[l, bi, bf]
}

run agregar_v1_biblioteca_inicialmente_vacia_caso_exito {
	some l: Libro, bi, bf: Biblioteca | agregar_v1[l, bi, bf] and (no bi.coleccion)
}

run agregar_v1_biblioteca_inicialmente_libros_caso_exito {
	some l: Libro, bi, bf: Biblioteca | agregar_v1[l, bi, bf] and (some bi.coleccion)
}

run agregar_v1_caso_no_exito {
	some l: Libro, disj bi, bf: Biblioteca | not agregar_v1[l, bi, bf]
}

// para agregar_v2, distinguimos los casos de éxito (ya que tiene éxito siempre).
// especificamos la condición que se tiene que cumplir para que éste sea el caso de exito mencionado.
// nótese que es el mismo que estaba como precondición en agregar_v1.
run agregar_v2_efectivamente_se_agrega {
	some l: Libro, bi, bf: Biblioteca | agregar_v2[l, bi, bf] and (l not in bi.coleccion)
}

// distinguimos ahora el caso donde el libro no se agrega, porque ya estaba.
run agregar_v2_no_se_agrega {
	some l: Libro, disj bi, bf: Biblioteca | agregar_v2[l, bi, bf] and (l in bi.coleccion)
}

---- Modelado de comportamiento dinámico: ELIMINAR ----

// predicado para eliminar un libro de la colección de una biblioteca.
// se deben cumplir las siguientes condiciones:
// 
pred eliminar [] {

}
