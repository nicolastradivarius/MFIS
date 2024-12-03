/** ------------------------        Frasco de Galletitas: nuevo átomo ---------------------------  **/

/** ----- modelo ------------------------------------------------------- **/
sig Frasco { contenido: set Galletita}  
abstract sig Galletita { }
sig Chocolate, Naranja, Coco extends Galletita { }
sig Rellena in Galletita { }
	

// Minima cantidad de galletitas por instancia 
/** dejar este fact: esta puesto solo con el efecto de generar 
instancias donde hayan galletitas de todos los sabores **/

fact { #Galletita >4 and some Chocolate and 
         some Naranja and some Coco and 
         some Rellena} 


/** ---- Facts ---- **/

fact{all f: Frasco | some f.contenido&Rellena implies f.contenido-Rellena in Coco}


/** ---- Predicados de cambio ---------------   **/

pred ComerUnaGalletita[f1,f2: Frasco]{
	-- precondición
	some f1.contenido and  
	-- poscondición
	(
		(some f1.contenido & Rellena) implies 
			(some g: f1.contenido & Naranja | f2.contenido = f1.contenido - g)
	) and 
	(
		(f1.contenido & Rellena) = none implies 
			(some g: f1.contenido | f2.contenido = f1.contenido - g)
	)
}


/** --------------------- (1) comandos validación  ---------------   **/



// Buscar una instancia que tenga sólamente galletitas de coco.
run FrascoSoloCoco {
	some f: Frasco | f.contenido in Coco and no f.contenido & Rellena
} for 14


---------------- Casos de éxito --------------------

// Caso éxito 1: no hay galletitas rellenas, y toma una al azar del frasco.
// No se encuentran irregularidades en las instancias generadas por el analizador.
run ComerUnaGalletitaCasoExito1 {
	some disj f1, f2: Frasco | 
		(no f1.contenido & Rellena) and
		ComerUnaGalletita[f1, f2]
} for 5

// Caso éxito 2: sí hay galletitas rellenas, y sí hay de naranja, por lo que toma una de naranja.
// No se encuentran irregularidades en las instancias generadas por el analizador.
run ComerUnaGalletitaCasoExito2 {
	some disj f1, f2: Frasco |
		(some f1.contenido & Rellena) and
		ComerUnaGalletita[f1, f2]
} for 5

// Caso éxito 3: sí hay galletitas rellenas, y NO hay de naranja, por lo que toma cualquiera de las otras.
// El analizador no encuentra instancias. Sin embargo, debería ser posible que elija una de las rellenas del resto.
run ComerUnaGalletitaCasoExito3 {
	some disj f1, f2: Frasco |
		(some f1.contenido & Rellena) and
		(no f1.contenido & Naranja) and
		ComerUnaGalletita[f1, f2]
} for 14


// Caso éxito 4: identificamos la única galletita de naranja que hay en un frasco con rellenas, debe desaparecer.
// El analizador no encuentra contraejemplos, lo cual era esperable.
check ComerUnaGalletitaCasoExito4 {
	all disj f1, f2: Frasco |
		(some f1.contenido & Rellena and #(f1.contenido & Naranja) = 1 and ComerUnaGalletita[f1, f2]) implies
			(no f2.contenido & Naranja)
} for 14

---------------- Casos de no éxito --------------------

// Caso no éxito 1: no hay galletitas en el frasco, por lo que no debería ser posible comer.
// El analizador no encuentra instancias, lo cual es esperable.
run ComerUnaGalletitaCasoNoExito1 {
	some disj f1, f2: Frasco |
		(no f1.contenido) and
		ComerUnaGalletita[f1, f2]
} for 14

// Caso no éxito 2: las cardinalidades de las galletitas no son consistentes.
// El analizador no encuentra instancias, lo cual es esperable.
run ComerUnaGalletitaCasoNoExito2 {
	some disj f1, f2: Frasco |
		#(f1.contenido) = 2 and
		ComerUnaGalletita[f1, f2] and
		#(f2.contenido) = 2
} for 14

// Caso no éxito 3: el frasco tiene rellenas, pero no tiene de naranja rellenas.
// Este caso en realidad no es posible porque si un frasco tiene galletitas rellenas, el resto de sus galletitas
// deben ser o bien otras rellenas, o también de coco. Por lo tanto, un frasco no puede tener galletitas rellenas
// y galletitas de naranja no-rellenas.
// El analizador no encuentra instancias como era de esperar.
run ComerUnaGalletitaCasoNoExito3 {
	some disj f1, f2: Frasco |
		some f1.contenido & Rellena and
		some f1.contenido & (Naranja-Rellena) and
		(no g: Rellena | g in f1.contenido and g in Naranja) and
		ComerUnaGalletita[f1, f2]
} for 14



/** --------------- (2) Corrección de la operación ------------------ */

pred ComerUnaGalletitaV2[f1, f2: Frasco] {
	-- precondición: el frasco debe tener galletitas.
	some f1.contenido and  
	-- poscondiciones:
	(
		-- si tiene galletitas rellenas, toma una de naranja (si hay).
		(some f1.contenido & Rellena and some f1.contenido & Naranja) implies 
			(some g: f1.contenido & Naranja | (g in Rellena) and f2.contenido = f1.contenido - g)
	) and 
	(
		-- si tiene rellenas pero NO tiene de naranja, toma una al azar
		(some f1.contenido & Rellena and no f1.contenido & Naranja) implies
			(some g: f1.contenido | f2.contenido = f1.contenido - g)
	) and
	(
		-- si no tiene galletitas rellenas, toma una al azar.
		(f1.contenido & Rellena = none) implies 
			(some g: f1.contenido | f2.contenido = f1.contenido - g)
	)
}


------------------ Casos de éxito ------------------


// Caso éxito 1: sí hay galletitas rellenas pero no hay de Naranja en el frasco.
// Se espera que se tome una galletita al azar.
// El analizador encuentra instancias regulares.
run ComerUnaGalletitaV2CasoExito1 {
	some disj f1, f2: Frasco |
		(some f1.contenido & Rellena) and
		(no f1.contenido & Naranja) and
		ComerUnaGalletitaV2[f1, f2]
} for 14

// Caso éxito 2: la cantidad de galletitas es 1, y la que hay es rellena.
// El analizador encuentra instancias regulares, donde `f2` ya no tiene galletitas.
run ComerUnaGalletitaV2CasoExito2 {
	some disj f1, f2: Frasco |
		(one f1.contenido) and
		(f1.contenido in Rellena) and
		ComerUnaGalletitaV2[f1, f2]
--		and no f2.contenido
} for 14


-------------- Casos de no éxito -------------------

// Caso no éxito 1: no hay galletitas en el frasco, por lo que no debería ser posible comer.
// El analizador no encuentra instancias, lo cual es esperable.
run ComerUnaGalletitaV2CasoNoExito1 {
	some disj f1, f2: Frasco |
		(no f1.contenido) and
		ComerUnaGalletitaV2[f1, f2]
} for 14

// Caso no éxito 2: las cardinalidades de las galletitas no son consistentes.
// El analizador no encuentra instancias, lo cual es esperable.
run ComerUnaGalletitaV2CasoNoExito2 {
	some disj f1, f2: Frasco, g: Galletita |
		one f1.contenido and
		g in f1.contenido and 
		ComerUnaGalletitaV2[f1, f2] and
		g in f2.contenido
} for 14
