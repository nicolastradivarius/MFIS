/* Sincronizacion de archivos en la nube

Modelo para un solo archivo */

open util/ordering[Estado] as ord

one sig Archivo { }

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

sig Estado {
	actualizacionesPendientes: set Actualizacion,
	// cambiamos la multiplicidad a `lone` para que sea consistente semánticamente.
	ultimaActualizacion: lone Actualizacion 
}
	
// minima cantidad de solicitudes \\
fact { #Actualizacion > 2 and #Prioritaria > 0 } 

// definicion de estado válido
fact {
	all e:Estado | 
		(e.actualizacionesPendientes & e.ultimaActualizacion) = none or
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} 

// Este hecho provoca que el analizador no encuentre instancias porque es una contradicción directa a la multiplicidad
// establecida para el campo `ultimaActualizacion`. Sigue siéndolo ahora que lo cambiamos a `lone`.
// Básicamente dice que no existen átomos en la relación, para cualquier estado.
--fact { all e:Estado | #(e.ultimaActualizacion) < 1 }


/**
Añadir al archivo resultante del inciso 2 la definición de la parte que involucra dinámica, que se 
encontraba originalmente comentada en el archivo del anexo. 
Validar el predicado AplicarUltimaActualizacion[e1,e2: Estado]. 
Asumir que los otros dos predicados de dinámica ya fueron validados y son correctos.
*/


fact traces { 
	Inicializar[ord/first] and
	all est: Estado-ord/last | let sigEst = est.next |
		LlegaActualizacion[est,sigEst] or
		AplicarUltimaActualizacion[est,sigEst] or
		AplicarActualizacionPrioritaria[est,sigEst] 
}

pred Inicializar[e: Estado] {
	(e.actualizacionesPendientes = none) and 
	(e.ultimaActualizacion = none)
}

pred LlegaActualizacion[e1,e2: Estado] {
	// no hay solicitudes
	some a: Actualizacion | 
		(
			(
				e1.actualizacionesPendientes = none and 
				e1.ultimaActualizacion = none and
				e2.actualizacionesPendientes = e1.actualizacionesPendientes and 
				e2.ultimaActualizacion = a
			)
		)
	or
	// hay solicitudes
	some a: Actualizacion | 
		(
			(
				e1.ultimaActualizacion != none and	
				a !in (e1.ultimaActualizacion + e1.actualizacionesPendientes) and
				e2.actualizacionesPendientes = e1.actualizacionesPendientes + e1.ultimaActualizacion and 
				e2.ultimaActualizacion = a 
			)
		)
}


/**
Es posible realizar la operación `AplicarUltimaActualizacion` si la solicitud almacenada en la relación 
`ultimaActualizacion` es prioritaria, o bien si no lo es pero no hay actualizaciones prioritarias pendientes. 
En caso de que la actualización aplicada sea prioritaria, se eliminan todas las actualizaciones pendientes. 
En caso de que la actualización aplicada no sea prioritaria, se coloca como `ultimaActualizacion` alguna de las
actualizaciones que estaban pendientes.
*/
pred AplicarUltimaActualizacion[e1,e2: Estado] {
	(
		// precondicion 1: la ultima actualizacion es prioritaria
		some e1.ultimaActualizacion & Prioritaria and
		// postcondicion 1: se eliminan todas las actualizaciones pendientes
		e2.actualizacionesPendientes = none and
		e2.ultimaActualizacion = none
	)
	or
	(
		// precondición 2: la ultima actualizacion es no prioritaria y no hay actualizaciones prioritarias pendientes
		some (e1.ultimaActualizacion & Actualizacion-Prioritaria) and
		no (e1.actualizacionesPendientes & Prioritaria) and
		// postcondicion 2: se elige alguna de las actualizaciones pendientes para colocarla como última
		(some a: e1.actualizacionesPendientes |
			(e2.actualizacionesPendientes = e1.actualizacionesPendientes - a) and
			(e2.ultimaActualizacion = a)
		)
	)
}

pred AplicarActualizacionPrioritaria[e1,e2: Estado] {
 	-- precondiciones
	(
		((e1.actualizacionesPendientes) & Prioritaria) != none   -- hay actualizaciones prioritarias pendientes
	) 
	and
	-- poscondiciones
	(
		some p: (e1.actualizacionesPendientes) & Prioritaria, e: e1.(^prev) | -- e1.^prev es lo mismo que prevs[e1]
			e.ultimaActualizacion = p and
			e2.actualizacionesPendientes = e1.actualizacionesPendientes - (e.actualizacionesPendientes + p) and
			e2.ultimaActualizacion = e1.ultimaActualizacion
	)
}

------------------- Validación de Dinámica ------------------------

run aplicarUltimaActualizacionCasoExitoDefault {
	some e1: Estado - ord/last | let e2 = e1.next |
		AplicarUltimaActualizacion[e1, e2]
} for 7

// Se aplica la ultima actualización en un caso donde la solicitud es prioritaria. 
// Se espera que en el estado de llegada, no haya actualizaciones pendientes.
check aplicarUltimaActualizacionCasoExito1 {
	all e1: Estado - ord/last, a: Prioritaria | let e2 = e1.next |
		(
			(a in e1.ultimaActualizacion and AplicarUltimaActualizacion[e1, e2])
			implies
			no e2.actualizacionesPendientes
		)
} for 15
// Ahora el analizador no encuentra contraejemplos.


// No se aplica la última actualización en el caso en que ésta no sea prioritaria pero sí haya prioritarias pendientes.
check aplicarUltimaActualizacionCasoNoExito1 {
	all e1: Estado - ord/last, a: Actualizacion - Prioritaria | let e2 = e1.next |
		(
			(a in e1.ultimaActualizacion and some (e1.actualizacionesPendientes & Prioritaria))
			implies
			not AplicarUltimaActualizacion[e1, e2]
		)
} for 15
// El analizador sigue sin encontrar contraejemplos.


// Buscamos una instancia donde en un estado haya prioritarias pendientes, pero no haya ultimas prioritarias (puede haber
// comunes) y sea posible aplicar la ultima actualizacion.
// Se espera que el analizador no encuentre instancias dado que no se puede aplicar la actualizacion en estas condiciones.
run aplicarUltimaActualizacionCasoNoExito1 {
	some e1: Estado - ord/last | let e2 = e1.next |
		some (e1.actualizacionesPendientes & Prioritaria) and 
		no (e1.ultimaActualizacion & Prioritaria) and 
		AplicarUltimaActualizacion[e1, e2]
} for 15
// El analizador no encuentra instancias.


----------------------------------------------

/**
Verificar la siguiente propiedad para todos los estados:
"Si se aplica una solicitud no prioritaria, no quedan solicitudes pendientes en el próximo estado."
*/
check AplicarSolicitudNoPrioritaria {
	all e1: Estado - ord/last, a: Actualizacion - Prioritaria | let e2 = e1.next |
		(a in e1.ultimaActualizacion and AplicarUltimaActualizacion[e1, e2])
		implies
		(no e2.actualizacionesPendientes)
} for 5
/*
El analizador encuentra un contraejemplo. Tiene sentido ya que la descripción de la operación dice que si se aplica
una solicitud que no es prioritaria, se va a elegir una de las pendientes para ponerla como última. Si hay varias
pendientes, entonces al quitar una seguirán habiendo pendientes.
*/
