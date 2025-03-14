/* Actualizacion de archivos en la nube  */

sig Archivo {
	pendientes: set Actualizacion
} 

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }
	
// minima cantidad de actualizaciones por instancia
fact { #Actualizacion > 2 } 

// no puede haber mas de dos actualizaciones prioritarias pendiente 
fact {all a: Archivo | #(a.pendientes & Prioritaria) < 3}

-- Aplicar Actualización: el predicado debe satifacerse en caso que haya una actualizacion pendiente.
-- si hay alguna prioritaria debe aplicarse esta.
-- en caso de no haber prioritarias aplica alguna de las anteriores.
pred AplicarActualizacion[a1, a2: Archivo]{
	-- precondición
	#a1.pendientes > 1 and
	-- poscondición
	(
		(some a1.pendientes & Prioritaria implies a2.pendientes = a1.pendientes - Prioritaria)  or
		((a1.pendientes & Prioritaria) = none implies some act: Actualizacion | a2.pendientes = a1.pendientes - act)
	)
}


----------------------- Validación del predicado AplicarActualizacion ---------------------

/**
La política de aplicación de las actualizaciones es aplicar una prioritaria, en caso de que haya alguna, 
y en caso contrario tomar al azar una de las solicitudes pendientes.
*/


// Caso éxito default
run AplicarActualizacionCasoExitoDefault {
	some a1, a2: Archivo | AplicarActualizacion[a1, a2]
}

/*
Irregularidades detectadas:
- los dos átomos no comparten las actualizaciones en algunas instancias. Si a2 es una evolución de a1, debería tenerlas (falta el marco)
- hay instancias donde a1 y a2 son el mismo átomo, con lo cual a2 nunca podría representar a a1 en el tiempo.
*/


// Caso éxito 1: hay una actualización prioritaria en las pendientes, aplica esa.
run AplicarActualizacionCasoExito1 {
	some disj a1, a2: Archivo | (some a1.pendientes & Prioritaria) and AplicarActualizacion[a1, a2]
}

/*
Irregularidades detectadas:
- los dos átomos siguen teniendo el mismo conjunto de pendientes.
- las mismas irregularidades de antes.
*/


// Caso éxito 2: no hay una actualizacion prioritaria entre las pendientes, así que aplica una al azar.
run AplicarActualizacionCasoExito2 {
	some disj a1, a2: Archivo | (no a1.pendientes & Prioritaria) and AplicarActualizacion[a1, a2]
}

/*
Irregularidades detectadas:
- el átomo 2 spawnea actualizaciones.
*/

// Caso éxito 3: hay dos actualizaciones prioritarias pendientes, debe aplicar una de ellas, y la otra permanecer en pendiente.
run AplicarActualizacionCasoExito3 {
	some disj a1, a2: Archivo |
		#(a1.pendientes & Prioritaria) = 2 and
		no (a1.pendientes & Actualizacion-Prioritaria) and
		AplicarActualizacion[a1, a2] and
		#(a2.pendientes & Prioritaria) = 1 and
		no (a2.pendientes & Actualizacion-Prioritaria)
}

/*
Irregularidades detectadas:
- los dos átomos de Archivo no comparten las actualizaciones.
*/

// Caso no éxito 1: el archivo no tiene actualizaciones pendientes, por lo que no debería verificarse el predicado.
// El analizador no encuentra instancias, lo cual es esperable.
run AplicarActualizacionCasoNoExito1 {
	some disj a1, a2: Archivo |
		(no a1.pendientes) and
		AplicarActualizacion[a1, a2]
} for 15

// Caso no éxito 2: las cardinalidades de las actualizaciones del archivo no son consistentes con el predicado.
run AplicarActualizacionCasoNoExito2 {
	some disj a1, a2: Archivo |
		#a1.pendientes = 2 and
		AplicarActualizacion[a1, a2] and
		#a2.pendientes = 3
} for 15

/*
El analizador encuentra instancias, contrario a lo esperado.
Irregularidades detectadas:
- se muestra claramente lo que se ha venido diciendo a lo largo de la validación: las actualizaciones de los dos átomos no son consistentes.
En este caso, se le agregó una actualización.
*/


// Caso éxito 4: verificamos que cuando se aplica la única actualización pendiente de un archivo, ya no tiene más.
// El analizador no encuentra contraejemplos.
check AplicarActualizacionCasoExito4 {
	all disj a1, a2: Archivo | 
		((one a1.pendientes) and AplicarActualizacion[a1, a2])
		implies
		(no a2.pendientes)
} for 15


// Caso éxito 5: similar al 4, verificamos que cuando se aplica la única actualización prioritaria pendiente de un archivo, ya no tiene más
check AplicarActualizacionCasoExito5 {
	all disj a1, a2: Archivo | 
		((one a1.pendientes & Prioritaria) and AplicarActualizacion[a1, a2])
		implies
		(no a2.pendientes & Prioritaria)
}

/*
El analizador encuentra contraejemplos:
- En el primero, no se respetan las cardinalidades descritas en el comando check.
*/
