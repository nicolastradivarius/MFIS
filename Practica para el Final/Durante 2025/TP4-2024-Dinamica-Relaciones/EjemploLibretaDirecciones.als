open util/ordering[Libro]

sig Direccion, Nombre { }

sig Libro {
	// cada nombre esta mapeado a cero o mas direcciones.
	// una direccion puede no tener algun nombre asociado con ella.
	anotaciones: Nombre -> Direccion
}

// inicialmente el libro no tiene anotaciones
pred init [l:Libro] {
	no l.anotaciones
}

fact {
	// el primer estado es el que cumple con la inicializacion.
	init[first]
}

pred agregar [b, b': Libro] {
	// existe un nombre y una direccion tal que no estaban previamente en las anotaciones
	// del libro y se procede a agregarlas.
	some n: Nombre, d: Direccion |
		(n->d) !in b.anotaciones and
   		b'.anotaciones = b.anotaciones + (n->d)
}

pred borrar [b, b': Libro] {
	// existe un nombre y una direccion tal que estaban previamente en las anotaciones
	// del libro y se procede a borrarlas.
	some n: Nombre, d: Direccion |
		(n->d) in b.anotaciones and
		b'.anotaciones = b.anotaciones - (n->d)
}

pred corregir [b, b': Libro]  {
	// existe un nombre y dos direcciones tal que una esta en el libro y la otra no, y la idea
	// es reemplazar la que esta en el libro por la que no lo esta.
	some n: Nombre, disj d1, d2: Direccion |
		(n->d1) in b.anotaciones and
		(n->d2) !in b.anotaciones and
		b'.anotaciones = b.anotaciones - (n->d1) + (n->d2)
	}


fact traces {
	// todos los estados (menos el ultimo) tienen transiciones a traves de la validez de alguno
	// de los tres predicados.
	all lib: Libro - last | let libSig = lib.next |
		agregar[lib,libSig] or
		borrar[lib,libSig] or
		corregir[lib,libSig] 
}


--------------- Validacion del modelo -----------------

run {} for 3

run agregarCasoExito {
	some l: Libro - last | agregar[l, l.next]
} for 5

run borrarCasoExito {
	some l: Libro - last | borrar[l, l.next] and #nexts[l] = 3
} for 5

run corregirCasoExito {
	some l: Libro - last | corregir[l, l.next]
} for 5


// Refinamos el caso anterior.
run agregarCasoExito2 {
	some disj l1: Libro - last, n: Nombre, d: Direccion | let l2 = l1.next |
		(n->d) !in l1.anotaciones and 
		agregar[l1, l2] and
		(n->d) in l2.anotaciones
} for 5


// Si la anotacion ya estaba agregada entonces existe algun estado anterior en donde se agrego.
check agregadaEnAlgunEstado {
	all lib: Libro, n: Nombre, d: Direccion |
		(n -> d) in lib.anotaciones implies (
			some libPrev: prevs[lib] | let libSig = libPrev.next |
				(n -> d) not in libPrev.anotaciones and
				(n -> d) in libSig.anotaciones
			)
} for 9


// Si hay una anotacion que desaparecio en algun estado, es por la operacion borrar[]
check borradaEnAlgunEstado {
	all l1: Libro - last |
		// si ocurrio la operacion de borrar, entonces
		borrar[l1, l1.next] implies (
			// hay alguna anotacion que estaba en el libro, y luego dejo de estar
			some libSig: nexts[l1], n: Nombre, d: Direccion |
				(n -> d) in l1.anotaciones and
				(n -> d) not in libSig.anotaciones
		)
} for 9


// Para que una anotacion desaparezca, tiene que haberse producido un borrado o correccion.
check borradaOCorregidaEnAlgunEstado {
	// para todas las anotaciones posibles se cumple que
	all n: Nombre, d: Direccion |
		// si existe un libro donde la anotacion estaba, y otro posterior donde dejo de estar
		(some l1: Libro - last, l2: nexts[l1]| 
			(n -> d) in l1.anotaciones and 
			(n -> d) not in l2.anotaciones
		) implies
			// entonces existen libros donde se efectuo la operacion de borrar o corregir
			(some l3: Libro - last | let l4 = l3.next | borrar[l3, l4] or corregir[l3, l4])
} for 7
// Aclaracion: no se busca chequear que la operacion haya borrado o corregido especificamente
// al par (n, d), sino que simplemente se hayan efectuado.


// Probamos si se satisface que: para corregir una entrada en el libro, esta debe haberse 
// agregado antes.
check modificarSiAgregueJustoAntes { 
	all lib: Libro - first - last |
		corregir[lib, lib.next] implies agregar[lib.prev, lib] 
} for 5
// La formulacion dice que debe agregarse justo en el estado anterior.
// Encuentra un contraejemplo en el que el estado implicado es el Libro3.
// En este caso, Libro3 tiene la anotacion (Nombre1, Direccion2) y se reemplaza por
// (Nombre1, Direccion1) tal como se ve en el Libro4. Sin embargo, esta anotacion no fue 
// agregada en el Libro2. Mas aun, ninguna anotacion fue agregada en el Libro2, porque 
// no se efectuo la operacion de agregar, sino solo la de corregir.
// En sintesis, este contraejemplo muestra un caso donde se efectuo la operacion
// corregir[Libro3, Libro4], pero no se efectuo la operacion agregar[Libro2, Libro3], por ende
// V => F y la implicacion es falsa.


// Version del check anterior donde vemos que se haya agregado en cualquier estado anterior.
check modificarSiAgregueAntes {
	all lib: Libro - first - last |
		corregir[lib, lib.next] implies 
			(some libPrev: prevs[lib] | agregar[libPrev, libPrev.next])
} for 8

