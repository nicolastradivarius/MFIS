sig Libro {
	paginas: some Pagina,
	primeraPagina: one Pagina,
	marcador: lone Marcador
}

sig Marcador {
	marca: one Pagina
}

sig Pagina {
	sigPagina: lone Pagina
}

fact "todo libro tiene sólo una última página" {
	all l: Libro | one p: Pagina | 
		p in l.paginas and no p.sigPagina
}

fact "una página no puede ser siguiente de sí misma (dir o indir)" {
	// p.*sigPagina es el conjunto de todas las páginas que pueden ser alcanzadas
	// partiendo de p (o sea, todas las páginas después de p) e incluyendo a p.
	// Si usara la clausura transitiva ^, no tendría el par (p, p) y por ende
	// el join de p.^sigPagina no devolvería, entre otras páginas, a p, permitiéndome
	// generar instancias. Dicho de otro modo, p siempre va a estar en el join con la 
	// clausura reflexivo-transitiva de la relación sigPagina porque ésta incluye 
	// el par (p, p) y el join devolvería p, haciendo que el fact sea inchequeable.
--	all p: Pagina | p !in p.*sigPagina
	all p: Pagina | p !in p.^sigPagina
}

fact "las paginas de un libro son las alcanzadas por la relación siguiente más la primera" {
	// ^sigPagina son todas las páginas que siguen después de cada página (no importa el libro).
	// Por ejemplo, si sigPagina = {(p0, p1), (p1, p2)} entonces 
	// ^sigPagina = {(p0, p1), (p1, p2), (p0, p2)} (se agrega el par (p0,p2) porque
	// p2 es alcanzada desde p0, o lo que es similar, p2 es una página siguiente a p0).
	// l.paginas.^sigPaginas son todas las páginas que siguen después de cada una de las
	// páginas del libro l. Esto siempre excluye a la primera página del libro, pues
	// por restricciones del modelo, una página no puede ser siguiente de sí misma, y si
	// se analiza ^sigPagina, p1 (la primera) nunca aparece como segunda componente de las tuplas.
	// Por ejemplo, si el libro l tiene de páginas a p1, p2, p3 y p4, entonces
	// sigPagina = {(p1,p2), (p2,p3), (p3,p4)}
	// ^sigPagina = {(p1,p2), (p2,p3), (p3,p4), (p1,p3), (p2,p4), (p1,p4)}
	// l.paginas = {p1, p2, p3, p4} son las páginas del libro l
	// l.paginas.^sigPagina = {p2, p3, p4} (págs sigs a p1, a p2, a p3 y a p4)
	all l: Libro | l.paginas = (l.paginas.^sigPagina) + l.primeraPagina
}

// Otra manera de representar este hecho es diciendo que si una página pertenece a un libro,
// entonces su página anterior y su página siguiente también. Esto sigue siendo válido para
// la primera y última página ya que los join resultan vacíos.
fact "si una página pertenece a un libro, su página anterior también" {
	all l: Libro, p: Pagina | (p in l.paginas) implies (sigPagina.p in l.paginas)
}
fact "si una página pertenece a un libro, su página siguiente también" {
	all l: Libro, p: Pagina | (p in l.paginas) implies (p.sigPagina in l.paginas)	
}

fact "no hay páginas sueltas" {
	all p: Pagina | some l: Libro | p in l.paginas
}

fact "la página marcada por el marcador de un libro debe pertenecer a dicho libro" {
	all l: Libro | l.marcador.marca in l.paginas
}

run situacion1 {#Pagina = 2 and no Marcador and one Libro}

// El marcador marca páginas pero no está presente en el libro.
run situacion2 {#Pagina = 3 and one Marcador and one Libro}

// Si queremos restringir que las páginas pertenezcan a un único libro, bloquearíamos dinámica.
// Necesitamos un átomo nuevo que represente el mismo libro pero con modificaciones en el marcador.


-------------- Dinámica --------------


// Colocar marcador: se agrega un marcador en la primera página de un libro que no tiene marcadores
pred colocarMarcador[li, lf: Libro, m: Marcador] {
	// precondiciones
	(no li.marcador) and -- el libro inicialmente no tiene marcadores
	// postcondiciones
	(m in lf.marcador) and -- el libro finalmente tiene un marcador
	(m.marca = lf.primeraPagina) and -- el marcador marca la primera página del libro
	// condición de marco
	li.paginas = lf.paginas and -- las páginas del libro siguen siendo las mismas
	li.primeraPagina = lf.primeraPagina	
}

// Quitar marcador
pred quitarMarcador[li, lf: Libro, m: Marcador] {
	// precondiciones 
	(one li.marcador) and -- el libro inicialmente tiene un marcador (puedo usar one xq sólo hay uno),
	-- lo correcto sería usar "some" si es que un libro pudiera tener más marcadores
	// postcondiciones
	(no lf.marcador) and -- el libro finalmente no tiene marcadores
	// condición de marco
	(li.paginas = lf.paginas) and -- las páginas siguen siendo las mismas
	(li.primeraPagina = lf.primeraPagina)
}

// Mover marcador: requiere que la página a la que se quiere mover no esté marcada.
pred moverMarcador[li, lf: Libro, p: Pagina] {
	// precondiciones
	(some li.marcador) and -- el libro inicialmente tiene un marcador
	(p in li.paginas) and -- la pagina a la que se quiere mover el marcador pertenece al libro
	(li.marcador.marca != p) and -- la página a marcar no está actualmente marcada por el marcador
	// postcondiciones
	(lf.marcador.marca = p) and -- el marcador pasa a marcar la página p
	// condición de marco
	(li.paginas = lf.paginas) and -- las páginas siguen siendo las mismas
	(li.primeraPagina = lf.primeraPagina)
--	(li.marcador = lf.marcador) -- el marcador sigue siendo el mismo porque sólo se cambió de lugar
// el problema que tiene esto es que un marcador sólo puede marcar cero o un páginas, y si
// digo que el marcador tiene que ser el mismo en ambos átomos, necesariamente tiene que marcar
// dos páginas: la previa en el libro inicial y la nueva en el libro final. Esto bloquea la dinámica.
// Una solución es permitir que un marcador marque cero o más páginas.
}

// Avanzar marcador: mueve el marcador de la página actual a la siguiente (si no es la última)
pred avanzarMarcador[li, lf: Libro] {
	// precondiciones
	(one li.marcador) and
	NoEsUltimaPagina[li.marcador.marca] and -- la página actualmente marcada no es la última
	// postcondiciones
	lf.marcador.marca = li.marcador.marca.sigPagina and -- se marca la página siguiente a la actual
	(li.paginas = lf.paginas) and -- las páginas siguen siendo las mismas
	(li.primeraPagina = lf.primeraPagina)
}

// Determina si la página parametrizada no es la última página de algún libro (si no tiene siguiente).
pred NoEsUltimaPagina[p: Pagina] {
-- one p2: Pagina | p.sigPagina = p2
	p.sigPagina != none
}

run colocarMarcadorCasoExito1 {
	some li, lf: Libro, m: Marcador | colocarMarcador[li, lf, m]
}

run colocarMarcadorCasoNoExito1 {
	some li, lf: Libro, m: Marcador | some (li.marcador & Marcador) and colocarMarcador[li, lf, m]
}


run quitarMarcadorCasoExito1 {
	some li, lf: Libro, m: Marcador | quitarMarcador[li, lf, m]
}

run quitarMarcadorCasoNoExito1 {
	some li, lf: Libro, m: Marcador | no Marcador and quitarMarcador[li, lf, m]
}

// un marcador colocado en un libro siempre comienza por la primera página.
run moverMarcadorCasoNoExito1 {
	some li, lf: Libro | moverMarcador[li, lf, li.primeraPagina]
} for 7


run moverMarcadorCasoExito1 {
	some li, lf: Libro, p: Pagina | moverMarcador[li, lf, p]
} 

run avanzarMarcadorCasoExito1 {
	some li, lf: Libro, p: Pagina | avanzarMarcador[li, lf]
}
