/**    ---------   Frasco de Galletitas: Version estático -------------------- **/


/** ----------------------------- modelo ------------------------------------------------------- **/
sig Frasco {
	contenido: some Galletita,
  	tipo: one TipoFrasco
}  

abstract sig TipoFrasco {  }

one sig Individual, Mixto extends TipoFrasco { }

abstract sig Galletita { }
sig Chocolate, Naranja, Coco extends Galletita { }
sig Rellena in Galletita { }
	
// Minima cantidad de galletitas por instancia 
/** dejar este fact: esta puesto solo con el efecto de generar 
instancias donde hayan galletitas de todos los sabores **/
fact {
	#Galletita >4 and 
	some Chocolate and 
	some Naranja and 
	some Coco and 
	some Rellena
} 

 

/** ------------- restricciones del modelo ------------------------------------------------ **/

fact{ all f: Frasco | some f.contenido & Rellena iff f.contenido-Rellena in Coco }
// ¿Imposibilita la existencia de galletitas de coco no-rellenas en un frasco sin galletitas rellenas?
// Entiendo que un frasco solo tiene galletitas de coco no rellenas si y sólo si tiene galletitas rellenas.
// Por algo en los otros incisos, no hay un "iff" sino un "implies".

fact{ all f: Frasco | f.tipo = Individual implies UnicoSabor[f.contenido] }



/** ----------- predicados auxiliares ---------------------------------------------------- **/

pred UnicoSabor[colGalletitas: set Galletita] {
		colGalletitas in Chocolate or 
		colGalletitas in Naranja or 
		colGalletitas in Coco 
}

/** --------------------- comandos validación  ---------------   **/

run default {} for 5

// Los frascos de tipo individual sólo tienen galletitas de un sólo tipo.
// Buscamos un caso donde esto no ocurra.
// El analizador no encuentra instancias. Está bien modelado.
run FrascoIndividualUnicasGalletitas {
	some f: Frasco | (f.tipo in Individual) and not UnicoSabor[f.contenido]
} for 9

// Las galletitas rellenas solo pueden estar en frascos que tengan galletitas rellenas y/o de Coco.
// El analizador no encuentra contraejemplos. Está bien modelado.
check GalletitasRellenasRestriccion {
	all g: Rellena, f: Frasco | 
		(g in f.contenido) implies (f.contenido in Rellena+Coco)
} for 9

// Buscar una instancia que tenga sólamente galletitas de coco.
// El analizador no encuentra instancias, pero debería ser posible tener frascos con esta descripción.
run FrascoSoloCoco {
	some f: Frasco | f.contenido in Coco and no f.contenido & Rellena
} for 14


// Buscar instancias donde el frasco esté vacío.
// El analizador no encuentra instancias. Sin embargo, la descripción del modelo dice que un frasco puede estar vacío.
// La situación está mal modelada en este aspecto.
run FrascoVacio {
	some f: Frasco | no f.contenido
} for 8
