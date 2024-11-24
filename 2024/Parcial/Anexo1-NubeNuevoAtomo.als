/* Actualizacion de archivos en la nube  */

sig Archivo { pendientes: set Actualizacion} 
sig Actualizacion { }
sig Prioritaria extends Actualizacion { }
	
// minima cantidad de actualizaciones por instancia
fact { #Actualizacion > 2 } 

// no puede haber mas de dos actualizaciones prioritarias pendiente 
fact {all a: Archivo | #(a.pendientes & Prioritaria) < 3}

-- Aplicar Actualización: el predicado debe satifacerse en caso que haya una actualizacion pendiente.
-- si hay alguna prioritaria debe aplicarse esta.
-- en caso de no haber prioritarias aplica alguna de las anteriores.
pred AplicarActualizacion[a1,a2: Archivo]{
	-- precondición
	#a1.pendientes > 1 and
	-- poscondición
	(
		(some a1.pendientes & Prioritaria implies a2.pendientes = a1.pendientes - Prioritaria)  or
		((a1.pendientes & Prioritaria) = none implies some act: Actualizacion | a2.pendientes = a1.pendientes - act)
	)
}

------------------ (1) Validación ------------------

/* Para empezar, analizando sintácticamente el modelo, la definición del predicado AplicarActualizacion utiliza
implicaciones lógicas conectadas mediante disyunciones lógicas (OR), lo cual es una muy mala idea debido a que
si en una de las implicaciones, su antecedente es falso, entonces se vuelve verdadera y el predicado se satisface.

Por otro lado, la primer implicación dice que si el archivo inicial tiene actualizaciones prioritarias pendientes, entonces
el archivo final tendrá las mismas actualizaciones que tenía el inicial *quitando* TODAS las prioritarias. Esto no es
el comportamiento buscado ya que sólo debería quitar una de ellas.

(*) Ver comando aplicarActualizacionCasoExito3

*/

run default {}

/**
La politica de aplicacion de las actualizaciones es aplicar una prioritaria, en caso de que haya alguna,
y en caso contrario tomar al azar una de las solicitudes pendientes.
*/

// Caso en que no haya actualizaciones prioritarias, debería aplicar otra actualización.
// En la primer instancia se detectan irregularidades:
//	- a1 y a2 son el mismo átomo, por lo que a2 nunca podría representar a a1 con las actualizaciones aplicadas.
// 	- a1 tiene tres actualizaciones pendientes, y como a2 es el mismo átomo, también tiene las tres pendientes.
run aplicarActualizacionCasoExito1 {
	some a1, a2: Archivo | no Prioritaria and AplicarActualizacion[a1, a2]
}

// Caso en que haya solo una actualización prioritaria, y dos normales, debería aplicar la prioritaria y seguir teniendo
// pendientes las normales.
// En la primera instancia, a1 y a2 siguen teniendo las mismas actualizaciones.
// En la segunda instancia, a2 no tiene actualizaciones pendientes mientras a1 tiene tres. Está fallando el 
// comportamiento del predicado, ya que no debería aplicarlas todas de una.
run aplicarActualizacionCasoExito2 {
	some disj a1, a2: Archivo | 
		(one a1.pendientes & Prioritaria) and
		#(a1.pendientes & Actualizacion-Prioritaria) = 2 and 
		AplicarActualizacion[a1, a2]
}

// Si hay dos actualizaciones prioritarias, deberia aplicar una sola, no las dos.
// Comprobamos si la cantidad de actualizaciones prioritarias pendientes disminuya en 1, y el resto siga igual.
// En la primera instancia, si bien se cumple lo pedido en este comando run, es debido al resto de las condiciones
// explicitadas, y no por el efecto de AplicarActualizacion, ya que si por ello fuese, el archivo a2 debería tener
// sólamente actualizaciones normales pendientes y ninguna de las prioritarias que tenía a1.
// Es probable que el predicado se satisfaga por que el antecedente de la segunda implicación se hace falso (ver (*)).
run aplicarActualizacionCasoExito3 {
	some disj a1, a2: Archivo | 
		(#(a1.pendientes & Prioritaria) = 2) and
		(#(a1.pendientes & Actualizacion-Prioritaria) = 3) and
		AplicarActualizacion[a1, a2] and
		(#(a2.pendientes & Prioritaria) = 1) and
		(#(a2.pendientes & Actualizacion-Prioritaria) = 3) 
} for 5

// El mismo caso de arriba, solo que forzamos a que el archivo no tenga una disminución en sus actualizaciones pendientes
// No debería encontrar instancias porque entonces significaría que no está bien definida la dinámica.
// Sin embargo, en la primera, ambos archivos tienen las mismas actualizaciones pendientes.
run aplicarActualizacionCasoNoExito1 {
	some disj a1, a2: Archivo | 
		(#(a1.pendientes & Prioritaria) = 2) and
		(#(a1.pendientes & Actualizacion-Prioritaria) = 3) and
		AplicarActualizacion[a1, a2] and
		(#(a2.pendientes & Prioritaria) = 2) and
		(#(a2.pendientes & Actualizacion-Prioritaria) = 3) 
} for 5

// Verificamos si al aplicar una actualización prioritaria en un archivo, luego ésta desaparece.
// Falla, encuentra un contraejemplo donde ambos átomos a1 y a2 comparten la actualizacion prioritaria pendiente.
// Además, a1 y a2 difieren en el resto de sus actualizaciones, cuando se supone deberían tener las mismas.
check aplicarActualizacionPrioritariaLaDesaparece {
	all disj a1, a2: Archivo |
		((one a1.pendientes & Prioritaria) and AplicarActualizacion[a1, a2]) implies (no a2.pendientes & Prioritaria)
}

// Caso donde hay actualizaciones prioritarias, y luego de aplicar la actualización, sigue habiendo las mismas.
// Este comando es similar al check anterior.
// Encuentra instancias, donde la situación con la prioritaria es similar a la del check anterior.
run aplicarActualizacionCasoNoExito2 {
	some disj a1, a2: Archivo |
		(one a1.pendientes & Prioritaria) and (one a2.pendientes & Prioritaria) and AplicarActualizacion[a1, a2]
}

// Caso donde no hay actualizaciones. No encuentra instancias, así que esta parte está bien.
run aplicarActualizacionCasoNoExito3 {
	some disj a1, a2: Archivo |
		(no Actualizacion) and AplicarActualizacion[a1, a2]
} for 7

-------------------- (2) Corrección del predicado --------------------


// Aplicar Actualización: el predicado debe satifacerse en caso que haya al menos una actualizacion pendiente.
// Si hay alguna prioritaria debe aplicarse una de ellas.
// En caso de no haber prioritarias, aplica alguna de las normales.
pred AplicarActualizacionCorregido[a1,a2: Archivo] {
	// Precondiciones:
	-- hay actualizaciones pendientes
	(some a1.pendientes) and
	// Postcondiciones:
	-- si en las actualizaciones pendientes hay prioritarias, se aplica una de ellas
	((some a1.pendientes & Prioritaria) implies (some p: Prioritaria | (p in a1.pendientes) and a2.pendientes = a1.pendientes - p)) and
	-- si en las actualizaciones pendientes NO hay prioritarias, se aplica una de las normales
	((no a1.pendientes & Prioritaria) implies (some p: Actualizacion-Prioritaria | (p in a1.pendientes) and a2.pendientes = a1.pendientes - p))	
}

// Caso donde hay una actualización prioritaria pendiente. Muestra instancias regulares.
run AplicarActualizacionCorregidoCasoExito1 {
	some a1, a2: Archivo | (one a1.pendientes & Prioritaria) and AplicarActualizacionCorregido[a1, a2]
}

// Caso donde no hay actualizaciones prioritarias. Muestra instancias regulares.
run AplicarActualizacionCorregidoCasoExito2 {
	some a1, a2: Archivo | (no a1.pendientes & Prioritaria) and AplicarActualizacionCorregido[a1, a2]
}

// Caso donde la cantidad de actualizaciones pendientes varía en más de 1 luego de aplicar una actualización.
// No encuentra instancias. Si la cardinalidad de las pendientes de a2 se cambia a 2, muestra instancias regulares.
run AplicarActualizacionCorregidoCasoNoExito1 {
	some a1, a2: Archivo | 
		#(a1.pendientes) = 3 and 
		AplicarActualizacionCorregido[a1, a2] and
		#(a2.pendientes) = 1
} for 7

// Caso donde no hay actualizaciones. No encuentra instancias y está bien porque al no haber ninguna
// actualización en el modelo, a1 no puede tener pendientes.
run AplicarActualizacionCorregidoCasoNoExito2 {
	some a1, a2: Archivo | no Actualizacion and AplicarActualizacionCorregido[a1, a2]	
} for 7
