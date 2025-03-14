/* Actualizacion de archivos en la nube  */

one sig Archivo { pendientes: set Actualizacion} 
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


/**
Como se está representando la din´amica para las actualizaciones de un solo archivo, ¿puede 
definirse la signatura Archivo como unitaria? Justifique su respuesta. Muestre el efecto de este 
cambio utilizando el analizador.

Respuesta: NO. Como se está utilizando la estrategia nuevo átomo para representar dinámica, forzar a que la signatura
Archivo tenga un solo átomo sería bloquear la dinámica, puesto que se necesitan al menos dos para mostrar su evolución
con el tiempo.
*/


// Caso éxito default.
// El analizador no encuentra instancias ni siquiera permitiendo que a1 y a2 sean el mismo átomo. Al ser un comando run tan simple
// es evidente que la dinámica está bloqueada (o en su defecto, que hay algún error en el predicado, pero eso no ocurre).
run AplicarActualizacionCorregidoCasoExitoDefault {
	some a1, a2: Archivo | AplicarActualizacionCorregido[a1, a2]
} for 15

