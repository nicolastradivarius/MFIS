/**
Sincronizacion de archivos en la nube. Modelo para un solo archivo.
Validación del modelo.
*/

open util/ordering[Estado] as ord

one sig Archivo { }

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

sig Estado {
	actualizacionesPendientes: set Actualizacion,
	// cambiamos la multiplicidad a one ya que sólo puede haber una ultima actualizacion
	ultimaActualizacion: one Actualizacion 
}
	
// minima cantidad de solicitudes \\
fact { #Actualizacion > 2 and #Prioritaria > 0 } 

// definicion de estado válido
fact {
	all e:Estado |
		(e.actualizacionesPendientes & e.ultimaActualizacion) = none or
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} 

// limitacion de la cantidad de solicitudes marcadas como última \\
// Este hecho hace que sea imposible generar instancias default. Básicamente dice que no hay ultimas actualizaciones.
// Lo comentamos para poder validar la estática.
--fact { all e:Estado | #(e.ultimaActualizacion) < 1 }

run default {}

// Para todos los Estados, la última actualización debería ser una.
// Encuentra un contraejemplo en la primer instancia,
// donde en uno de los estados hay dos actualizaciones prioritarias marcadas como últimas.
check soloUnaUltimaActualizacion {
	all e: Estado | one e.ultimaActualizacion
} 

// Una actualización no puede estar pendiente y marcada como última al mismo tiempo.
check noActualizacionPendienteYUltima {
	all e: Estado | no a: Actualizacion | a in e.actualizacionesPendientes and a in e.ultimaActualizacion
} for 7




---------------------------- Dinamica ----------------------------

fact traces { 
		Inicializar[ord/first] and
		all est: Estado-ord/last | let sigEst=est.next |
			LlegaActualizacion[est,sigEst] or
             		AplicarUltimaActualizacion[est,sigEst] or
             		AplicarActualizacionPrioritaria[est,sigEst] 
	}

pred Inicializar[e: Estado] {
//	e.actualizacionesPendientes=none and 
//	e.ultimaActualizacion=none
	some e.actualizacionesPendientes and
	some e.ultimaActualizacion

}

pred LlegaActualizacion[e1,e2: Estado] {
	// no hay solicitudes
	some a: Actualizacion | (
		(e1.actualizacionesPendientes=none and 
		e1.ultimaActualizacion=none and
		e2.actualizacionesPendientes=e1.actualizacionesPendientes and 
		e2.ultimaActualizacion=a )
           )
	or
	// hay solicitudes
	some a: Actualizacion | (
		(e1.ultimaActualizacion!=none and
		a!in (e1.ultimaActualizacion + e1.actualizacionesPendientes) and
		e2.actualizacionesPendientes=e1.actualizacionesPendientes+e1.ultimaActualizacion and 
		e2.ultimaActualizacion=a )
    )
}

/**
Aplicacion de la ultima solicitud de actualizacion: Es posible realizar la operacion
AplicarUltimaActualizacion si la solicitud almacenada en la relacion ultimaActualizacion es
prioritaria, o bien si no lo es pero no hay actualizaciones prioritarias pendientes. En caso de
que la actualizacion aplicada sea prioritaria, se eliminan todas las actualizaciones pendientes.
En caso de que la actualizacion aplicada no sea prioritaria, se coloca como ultimaActualizacion
alguna de las actualizaciones que estaban pendientes
*/
pred AplicarUltimaActualizacion[e1,e2: Estado] {
	//precondiciones
	e1.ultimaActualizacion != none and  -- hay una actualización para aplicar 
	( 
		( 	( e1.ultimaActualizacion in (Actualizacion-Prioritaria) ) and -- la ultima actualizacion es no prioritaria y
			(e1.actualizacionesPendientes & Prioritaria) = none    -- no hay actualizaciones prioritarias pendientes
	         )
		or
		(	e1.ultimaActualizacion in Prioritaria   -- la ultima actualizacion es prioritaia
		)
	) and  
	// poscondiciones
	 (
		((e1.ultimaActualizacion in Prioritaria) implies (AplicarActualizacionPrioritaria[e1, e2])) and
		((e1.ultimaActualizacion in (Actualizacion-Prioritaria)) implies 
				(some a: (e1.actualizacionesPendientes) |
						(e2.actualizacionesPendientes = e1.actualizacionesPendientes - a) and 
						(e2.ultimaActualizacion = a))
		)
	)
}

pred AplicarActualizacionPrioritaria[e1,e2: Estado] {
 	-- precondiciones
         (  (  (e1.actualizacionesPendientes)&Prioritaria) != none ) and  -- hay actualizaciones prioritarias pendientes
         -- poscondiciones
	(
	some p: (e1.actualizacionesPendientes)&Prioritaria, e: e1.(^prev) | 
			e.ultimaActualizacion = p and
			e2.actualizacionesPendientes = e1.actualizacionesPendientes - (e.actualizacionesPendientes+p) and
			e2.ultimaActualizacion = e1.ultimaActualizacion
	)
}

// No genera instancias. Debe haber una contradicción en el predicado.
// Se debe a que el estado inicial define que no hay ultima actualizacion ni pendientes, asi que nunca va a ser
// posible aplicar alguna. Se pueden conseguir instancias modificando el predicado Inicializar.
// En ese caso, en la primer instancia se detecta la irregularidad de que la ultima actualización es prioritaria,
// y luego de aplicarla, no se eliminan las pendientes.
run aplicarUltimaActualizacionCasoExito {
	some e: Estado | let e2 = e.next | AplicarUltimaActualizacion[e, e2]
} for 7
