/** ---------------------------- Modelo ---------------------------- **/

one sig Frasco {
	var contenido: set Galletita
}

sig Galletita {}

sig Chocolate, Naranja, Coco in Galletita {}

sig Mixta in Galletita {}


fact "las galletitas mixtas son de dos sabores a la vez y siempre tienen chocolate" {
	// si una galletita es de chocolate y ademas de Naranja o Coco, entonces es Mixta
	(all m: Galletita | esMixta[m] implies (m in Mixta))
	and
	// todas las galletitas mixtas tienen Chocolate y de alguno de los otros sabores
	(all m: Mixta | esMixta[m])
}

fact init {
	no Frasco.contenido
}

fact "los frascos estan vacios o tienen galletitas de un solo tipo" {
	all f: Frasco |
		always {
			(no f.contenido) or
			(f.contenido = Chocolate) or
			(f.contenido = Naranja) or
			(f.contenido = Coco) 
		}
}

fact "cualquier otra galletita que no sea mixta, no puede tener varios sabores a la vez" {
	no g: Galletita - Mixta |
		(g in Chocolate & Naranja) or
		(g in Chocolate & Coco) or
		(g in Naranja & Coco) or
		(g in Chocolate & Naranja & Coco)
}



/** ---------------------------- Predicados & Funciones ---------------------------- **/



// una galletita es mixta si:
// 	- tiene chocolate obligatoriamente
// 	- tiene o bien naranja o bien coco, no ambos.
pred esMixta [g: Galletita] {
	(g in Chocolate) and 
	(g in Naranja+Coco) and
	(g not in Chocolate & Naranja & Coco)
}

/*
// devuelve el conjunto de galletitas mixtas
fun galletitasMixtas: set Galletita {
	{g: Galletita | esMixta[g]}
}
*/



/** ---------------------------- Run ---------------------------- **/

run galletitaNoMixtaConVariosSabores {
	some g: Galletita | 
		(g not in Mixta) and
		(g in Chocolate) and
		(g in Naranja)
} for exactly 5 Galletita

// alguna galletita mixta que tenga chocolate y no tenga naranja
run hayMixtas {some Mixta}

run frascoConGalletitas {
	some f: Frasco | eventually some f.contenido
} for exactly 6 Galletita

run frascoConGalletitasDeDistintosSabores {
	some f: Frasco | eventually some (f.contenido & (Chocolate+Naranja))
} for exactly 6 Galletita


/** ---------------------------- Aserciones ---------------------------- **/

/*
check funEqualMixta {
	galletitasMixtas = Mixta
}
*/

// toda galletita que sea mixta y no tenga naranja, necesariamente tiene coco
check {
	all g: Galletita | 
		(g not in Naranja and g in Mixta) implies (g in Coco)
}

check todaGalletitaMixtaTieneChocolate {
	all g: Galletita |
		(g in Mixta) implies (g in Chocolate)
}

