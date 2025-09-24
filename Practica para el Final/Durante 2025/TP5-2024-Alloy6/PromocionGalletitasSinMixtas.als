/** ---------------------------- Modelo ---------------------------- **/

one sig Frasco {
	var contenido: set Galletita
}

abstract sig Galletita {}

sig Chocolate, Naranja, Coco extends Galletita {}

fact "el frasco contiene galletitas todas del mismo sabor" {
	all f: Frasco | 
		((some f.contenido & Chocolate) implies (f.contenido = Chocolate)) and
		((some f.contenido & Naranja) implies (f.contenido = Naranja)) and
		((some f.contenido & Coco) implies (f.contenido = Coco)) 
}


fact init {
	#Frasco.contenido = 5
}

fact traces {
	always {
		hacerNada or
		(some f: Frasco | comerGalletita[f])
	}
}



/** ---------------------------- Predicados & Funciones ---------------------------- **/


// Modela el comportamiento de tomar una galletita del frasco para comerla
pred comerGalletita[f: Frasco] {
	some g: Galletita |
		(g in f.contenido) and
		f.contenido' = f.contenido - g
}

pred hacerNada[] {
	all f: Frasco |
		f.contenido' = f.contenido
}


/** ---------------------------- Run ---------------------------- **/

run default {eventually some contenido} for 6

run frascoConChocolate {
	some Frasco.contenido and Frasco.contenido = Chocolate
} for 6



run frascoConGalletitas {
	some f: Frasco | eventually some f.contenido
} for exactly 6 Galletita

run frascoConGalletitasDeDistintosSabores {
	some f: Frasco | eventually {
		some (f.contenido & Chocolate) and
		some (f.contenido & Naranja)
	}
} for exactly 6 Galletita


// Verificar si es posible que en algun momento las galletitas disponibles sean menos que
// las que hay al comienzo.
run menosGalletitasQueAlComienzo1 {
	some Frasco.contenido and eventually no Frasco.contenido
} for exactly 6 Galletita

run menosGalletitasQueAlComienzo2 {
	eventually #(Frasco.contenido) = 3 and eventually #(Frasco.contenido) = 2
} for exactly 6 Galletita


/** ---------------------------- Aserciones ---------------------------- **/

// Toda galletita que es comida estuvo previamente en el frasco.
check galletitaComidaEstuvoEnFrasco {
	always {
		all f: Frasco, g: Galletita |
			(eventually g not in f.contenido) implies (once g in f.contenido)
	}
-- si hay un estado en el que la galletita no esta en el frasco, entonces estuvo en alguno previo
} for exactly 6 Galletita
