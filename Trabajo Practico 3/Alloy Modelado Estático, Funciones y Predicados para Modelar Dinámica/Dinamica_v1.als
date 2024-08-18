sig Biblioteca {
	coleccion: set Libro
}

sig Libro {
	escritoPor: set Autor,
	genero: one GeneroLiterario
}

// puede haber autores que no sean novelistas, poetas, etc.
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

// no es posible que haya novelistas y poetas que escriban libros en común.

fact "novelistas y poetas no son autores de los mismos libros" {
	escritoPor.Novelista & escritoPor.Poeta = none
}


/*
// forma alternativa de escribirlo (aunque las variables de Alloy cambien).
// no es necesario aclarar que a1 y a2 es disj ya que, por la forma en que
// está definido nuestro modelo, no hay un mismo autor que sea Novelista y Poeta
// al mismo tiempo (por el extends).

fact "novelistas y poetas no son autores de los mismos libros" {
	all l: Libro | 
		no a1, a2: Autor |
			(a1 in Novelista) and
			(a2 in Poeta) and
			(a1 in l.escritoPor) and
			(a2 in l.escritoPor)
}

/*
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


run autor_novelistaypoeta {
	some l: Libro |
		(l in escritoPor.Novelista) and
		(l in escritoPor.Poeta)
} for 6

check libro_con_autor_no_novelistaypoeta {
	all l: Libro |
		(some l.escritoPor) implies
			(
				((l.escritoPor in Poeta) implies (l.escritoPor not in Novelista)) and
				((l.escritoPor in Novelista) implies (l.escritoPor not in Poeta))
			)
} for 10

run libro_novelista_poeta_periodista {
	some l: Libro | 
		(some l.escritoPor) and
		(l.escritoPor in Novelista) and
		(l.escritoPor in Poeta) and
		(l.escritoPor in Periodista)
} for 10

// otra forma alternativa de expresar el hecho es usando funciones que permitan
// factorizar expresiones dentro de la restricción (y que podamos reusar), de la
// misma forma que usábamos predicados para factorizar condiciones booleanas.
// definimos una función para obtener el conjunto de autores de un libro.
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

// Funcion para obtener autores de una clase dada.
// hacemos esto con el fin de evitar escribir una función por cada tipo de Autor.
// directamente le "pasamos" como argumento el tipo de autor que queremos a la función.
// esta función es más expresiva.
// Notese que autores_clase[l, Autor] es equivalente a autores[l] ya que ambas devuelven
// el conjunto de autores de l. Lo probamos con la aserción más adelante.
fun autores_clase [l: Libro, clase: set Autor]: set Autor {
	autores[l] & clase
}

// creemos que la función `autores` es equivalente a la función `autores_clase` con el arg Autor.
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
