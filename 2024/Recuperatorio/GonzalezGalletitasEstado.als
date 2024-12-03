/**  ---------------      Frasco de Galletitas: Estados ----------------------------   **/

open util/ordering[Estado] as ord

one sig Frasco { }

abstract sig Galletita { }
sig Chocolate, Naranja, Coco extends Galletita { }

abstract sig TipoFrasco { }
one sig Mixto, Individual extends TipoFrasco { }

sig Estado {
	contenido: set Galletita,
	etiqueta: one TipoFrasco
}
	
/** --------------------------- facts ------------------------------------------------------------------------ **/
// Minima cantidad de galletitas por instancia 
/** dejar este fact: esta puesto solo con el efecto de generar instancias donde 
hayan galletitas de todos los sabores **/
fact { #Galletita >4 and some Chocolate and some Naranja and some Coco} 


// -----------------------  fact traces --------------------------------

fact traces { inicializar[ord/first] and
		all est: Estado-ord/last | let sigEst=est.next |
--			agregarGalletita[est,sigEst] or
			agregarGalletitaV2[est,sigEst] or
            comerGalletita[est,sigEst] or
			cambiarEtiqueta[est,sigEst]
}


/**  ----------------------------------------------------------------------------------------------
        El frasco mantiene su tipo desde el comienzo 
---------------------------------------------------------------------------------------------- **/

pred inicializar[e: Estado] {
	e.contenido = none 
}

/**  ----------------------------------------------------------------------------------------------------------------
         Se pueden agregar galletitas, no se puede modificar el tipo de frasco
------------------------------------------------------------------------------------------------------------------- **/

pred agregarGalletita[e1,e2: Estado] {
	( e1.etiqueta = Mixto implies
		(	some g: Galletita | e2.contenido = e1.contenido + g 
		)
          ) and
	( e1.etiqueta = Individual implies
		( some g:Galletita |
			(   e2.contenido in Chocolate or 
			    e2.contenido in Naranja  or 
			    e2.contenido in Coco
			) and  e2.contenido = e1.contenido + g 
 		)
	)
}

/**  ------------------------------------------------------------------------------------------------------
         Comer quita una galletita cualquiera del frasco
----------------------------------------------------------------------------------------------------------- **/

pred comerGalletita[e1,e2: Estado] {
	// el frasco tiene galletitas
	some g: e1.contenido | 
		 e2.contenido = e1.contenido - g and
	e1.etiqueta= e2.etiqueta
}	

/**  --------------------------------------------------------------------------------------------------------
         Cambiar etiqueta cambia un frasco rotulado como mixto a individual
--------------------------------------------------------------------------------------------------------------- **/

pred cambiarEtiqueta[e1,e2: Estado] {
	e1.etiqueta = Mixto and 
        UnicoSabor[e1.contenido] and 
        e2.etiqueta= Individual and
	e2.contenido = e1.contenido
}

/** --------------------- predicados auxiliares ----------------------------------------- **/

pred UnicoSabor[colGalletitas: set Galletita]{
		colGalletitas in Chocolate or 
		colGalletitas in Naranja or 
		colGalletitas in Coco 
}



/** -----------------------------------------------------
        (1) Comandos de validacion agregarGalletita
---------------------------------------------------------- **/


-------------- Casos de éxito ------------------

// Caso éxito 1: se agregó una galletita a un frasco de tipo individual.
/*
Se detectan irregularidades en la primer instancia:
- "e1" es identificado como el Estado1, por ende "e2" es Estado2. Después de aplicar la operación, no se agregó 
algo al frasco, sino que cambió su etiqueta de Individual a Mixto. Este no es el comportamiento esperado.
*/
run agregarGalletitaCasoExito1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		agregarGalletita[e1, e2]
} for 5

// Caso éxito 1.1: se fuerza a que el frasco tenga galletitas.
// El frasco no cambia de etiqueta ahora, pero no se le agregó alguna galletita también.
run agregarGalletitaCasoExito1_1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		some e1.contenido and
		agregarGalletita[e1, e2]
} for 5


// Caso éxito 1.2: se fuerza a que el frasco NO tenga galletitas.
/*
En la segunda instancia se detectan irregularidades:
	- "e1" es el Estado1. Si bien se agrega una galletita de Coco, también se cambia la etiqueta del frasco.
*/
run agregarGalletitaCasoExito1_2 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		no e1.contenido and
		agregarGalletita[e1, e2]
} for 5

// Caso no éxito 1: el frasco es individual y se agrega una galletita que no es del tipo que ya tiene.
// El analizador no encuentra instancias, lo cual era esperable.
run agregarGalletitaCasoNoExito1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		some e1.contenido and
		agregarGalletita[e1, e2] and
		not UnicoSabor[e2.contenido]
} for 5

// Caso no éxito 2: el frasco tiene la maxima cantidad de galletitas según el scope y no se debería poder agregar más.
// Si se deja el scope en el mismo número que #e1.contenido, el analizador no encuentra instancias, lo cual es
// esperable. Sin embargo, si el scope se cambia a un número más grande, se vuelven a ver las irregularidades.
// Por ejemplo, ahora como está escrito, la irregularidad se aprecia en el estado 23.
run agregarGalletitaCasoNoExito2 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		#e1.contenido = 6 and
		agregarGalletita[e1, e2]
} for 25

// Caso no éxito 3: agregar una galletita que ya estaba en el frasco.
// El analizador encuentra instancias, contrario a lo esperable. 
run agregarGalletitaCasoNoExito3 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		agregarGalletita[e1, e2] and
		e1.contenido = e2.contenido
--		and e1.etiqueta = e2.etiqueta -- si se fuerza, se evidencia aún más que no se agrega ninguna galletita.
} for 5


/** -----------------------------------------------------
        (2) Corrección predicado agregarGalletita
---------------------------------------------------------- **/


pred agregarGalletitaV2[e1, e2: Estado] {
	(e1.etiqueta = Mixto implies (some g: Galletita-e1.contenido | e2.contenido = e1.contenido + g )) and
	(e1.etiqueta = Individual implies (some g: Galletita-e1.contenido | e2.contenido = e1.contenido + g and UnicoSabor[e2.contenido])) and
	-- marco
	e1.etiqueta = e2.etiqueta
}


// Caso éxito 1: se agregó una galletita a un frasco de tipo individual.
// El analizador encuentra instancias regulares.
run agregarGalletitaV2CasoExito1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		agregarGalletitaV2[e1, e2]
} for 5

run $1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1 = ord/first and
		e1.etiqueta = Individual and
		not UnicoSabor[e1.contenido] and
		agregarGalletitaV2[e1, e2]
} for 5

// Caso éxito 1.1: se fuerza a que el frasco tenga galletitas.
// El analizador encuentra instancias regulares.
run agregarGalletitaV2CasoExito1_1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		some e1.contenido and
		agregarGalletitaV2[e1, e2]
} for 5


// Caso éxito 1.2: se fuerza a que el frasco NO tenga galletitas.
// El analizador encuentra instancias regulares.
run agregarGalletitaV2CasoExito1_2 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1 = ord/first and
		e1.etiqueta = Individual and
		no e1.contenido and
		agregarGalletitaV2[e1, e2]
} for 5

// Caso no éxito 1: el frasco es individual y se agrega una galletita que no es del tipo que ya tiene.
// El analizador no encuentra instancias, lo cual era esperable.
run agregarGalletitaV2CasoNoExito1 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		some e1.contenido and
		agregarGalletitaV2[e1, e2] and
		not UnicoSabor[e2.contenido]
} for 14

// Caso no éxito 2: el frasco tiene la maxima cantidad de galletitas según el scope y no se debería poder agregar más.
// El analizador no encuentra instancias, lo cual era esperable.
run agregarGalletitaV2CasoNoExito2 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		#e1.contenido = 6 and
		agregarGalletitaV2[e1, e2]
} for 6

// Caso no éxito 3: agregar una galletita que ya estaba en el frasco.
// El analizador no encuentra instancias, que era esperable, a diferencia de antes.
run agregarGalletitaV2CasoNoExito3 {
	some e1: Estado-ord/last | let e2 = e1.next |
		e1.etiqueta = Individual and
		agregarGalletitaV2[e1, e2] and
		e1.contenido = e2.contenido
} for 19


/** -----------------------------------------------------
        (3) Verificación de propiedad 1
---------------------------------------------------------- **/

/** Si el contenido del frasco no es vacío entonces el frasco está etiquetado como mixto. */
/*
El analizador encuentra contraejemplos. En el primero, se puede ver que a partir del estado 2, el frasco cambia su etiqueta
a Individual, teniendo contenido único dentro, y por lo tanto, la propiedad no se satisface.
Si en el fact traces, eliminamos la operación cambiarEtiqueta, de modo que la transición entre estados sea por las otras
dos operaciones, entonces se puede ver que en la primera instancia, en el Estado1, ni bien se agrega una galletita, 
el frasco sigue siendo Individual y no Mixto.
*/
check propiedad1 {
	all e: Estado | some e.contenido implies e.etiqueta = Mixto
} for 5



/** -----------------------------------------------------
        (4) Verificación de propiedad 2
---------------------------------------------------------- **/

/** 
Si el frasco está etiquetado como individual, en todos los estados siguientes, tiene galletitas del mismo sabor o está vacío. 
*/ 
/*
El analizador encuentra contraejemplos.
En el primero:
- el frasco está vacío hasta que en el estado 2 se agregó una galletita de Naranja, luego en el Estado3 desaparece, y en el
Estado4 tiene una galletita de Chocolate. Por lo tanto, no se mantuvo con galletitas del mismo sabor. Además, tampoco se
mantuvo vacío.

Si se fuerza a que no haya estados siguientes, la única manera de que se cumpla eso es que el estado sea el último, y en
ese caso, el analizador no encuentra contraejemplos, lo cual es esperable porque si se empieza a analizar la propiedad
a partir del último estado, no hay manera de garantizar su cumplimiento para los siguientes.

Nota: aparentemente está mal usar "let" cuando se trabaja con un conjunto, como nexts[e]. La versión "corregida"
está en el check de propiedad2_caso2, sin embargo, el analizador no encuentra contraejemplos allí.
Desconozco cual de las dos formas es la correcta, pero por intuición, la propiedad debería ser falsa, ya que es posible que
a un frasco se le quite una galletita para comerla, y luego se le ponga otra de otro tipo.
*/
check propiedad2 {
	all e: Estado | let esigs = nexts[e] |
--		no esigs and
		(e.etiqueta = Individual) implies (
			UnicoSabor[esigs.contenido] or
			no esigs.contenido
		)
} for 5

check propiedad2_caso2 {
	all e1: Estado - ord/last, e2: nexts[e1] |
		(e1.etiqueta = Individual) implies (
			UnicoSabor[e2.contenido] or
			no e2.contenido
	)
} for 5
