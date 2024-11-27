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
pred AplicarActualizacion[a1, a2: Archivo]{
	-- precondición
	#a1.pendientes > 1 and
	-- poscondición
	(
		(some a1.pendientes & Prioritaria implies a2.pendientes = a1.pendientes - Prioritaria)  or
		((a1.pendientes & Prioritaria) = none implies some act: Actualizacion | a2.pendientes = a1.pendientes - act)
	)
}

-------------------- Nuevo predicado -------------------------


/**
La política de aplicación de las actualizaciones es aplicar una prioritaria, en caso de que haya alguna, 
y en caso contrario tomar al azar una de las solicitudes pendientes.
*/


pred AplicarActualizacionCorregido[a1, a2: Archivo] {
	-- precondiciones: que haya actualizaciones pendientes para a1
	some (a1.pendientes) and
	-- postcondiciones: si en las pendientes hay prioritarias, hay que aplicar una de ellas.
	(some a1.pendientes & Prioritaria implies (some a: a1.pendientes & Prioritaria | a2.pendientes = a1.pendientes - a)) and
	(no a1.pendientes & Prioritaria implies (some a: a1.pendientes | a2.pendientes = a1.pendientes - a))
}



---------------- Validación del nuevo predicado ----------------------

// Caso éxito default.
run AplicarActualizacionCorregidoCasoExitoDefault {
	some disj a1, a2: Archivo | AplicarActualizacionCorregido[a1, a2]
}

// Caso éxito 1: si a1 tiene 1 actualiazción prioritaria y 2 comunes, luego de la operación, sólo tiene 2 comunes.
// El analizador no encuentra contraejemplos, lo cual era esperable.
check AplicarActualizacionCorregidoCasoExito1 {
	all disj a1, a2: Archivo | 
		(#(a1.pendientes & Prioritaria) = 1 and #(a1.pendientes & (Actualizacion-Prioritaria)) = 2 and AplicarActualizacionCorregido[a1, a2])
		implies
		(#(a2.pendientes & Prioritaria) = 0 and #(a2.pendientes & (Actualizacion-Prioritaria)) = 2)
} for 15

// Caso no éxito 1: a1 tiene una actualizacion prioritaria y otras comunes, y luego de la operación, tiene una actualizacion comun menos.
// El analizador no encuentra instancias, lo cual es de esperar, porque si había una prioritaria, tenía que aplicar esa.
run AplicarActualizacionCorregidoCasoNoExito1 {
	some disj a1, a2: Archivo | 
		#(a1.pendientes & Prioritaria) = 1 and
		#(a1.pendientes & (Actualizacion-Prioritaria)) = 2 and
		AplicarActualizacionCorregido[a1, a2] and
		#(a2.pendientes & Prioritaria) = 1 and
		#(a2.pendientes & (Actualizacion-Prioritaria)) = 1
} for 15

// Caso no éxito 2: el archivo no tiene actualizaciones pendientes, por lo que no debería verificarse el predicado.
// El analizador no encuentra instancias, lo cual es esperable.
run AplicarActualizacionCorregidoCasoNoExito2 {
	some disj a1, a2: Archivo |
		(no a1.pendientes) and
		AplicarActualizacionCorregido[a1, a2]
} for 15
