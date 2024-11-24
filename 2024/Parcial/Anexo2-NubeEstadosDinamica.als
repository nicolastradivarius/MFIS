/* Sincronizacion de archivos en la nube

Modelo para un solo archivo */

open util/ordering[Estado] as ord

one sig Archivo { }

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

sig Estado {
	actualizacionesPendientes: set Actualizacion,
	ultimaActualizacion: some Actualizacion 
}
	
// minima cantidad de solicitudes \\
fact { #Actualizacion >2 and #Prioritaria >0 } 

// definicion de estado válido
fact {
	all  e:Estado | 
		(e.actualizacionesPendientes & e.ultimaActualizacion) = none or
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} 

// limitacion de la cantidad de solicitudes marcadas como última \\
fact { all e:Estado | #(e.ultimaActualizacion) < 1 }



/* --------------------------------------------------------------------------------------------------------------------------------------------------------------------

Definicion de facts y predicados para modelar dinámica

Descomentar para el inciso 4

------------------------------------------------------------------------------------------------------------------------------------------------------------------------ */
 /*
fact traces { Inicializar[ord/first] and
		all est: Estado-ord/last | let sigEst=est.next |
			LlegaActualizacion[est,sigEst] or
             		AplicarUltimaActualizacion[est,sigEst] or
             		AplicarActualizacionPrioritaria[est,sigEst] 
	}

pred Inicializar[e: Estado] {
	e.actualizacionesPendientes=none and 
	e.ultimaActualizacion=none
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

pred AplicarUltimaActualizacion[e1,e2: Estado] {
	//precondiciones
	e1.ultimaActualizacion !=none and  -- hay una actualización para aplicar 
	( 
		( 	( e1.ultimaActualizacion in (Actualizacion-Prioritaria)) and -- la ultima actualizaciones no prioritaria y
			(e1.actualizacionesPendientes&Prioritaria)=none    -- no hay actualizaciones prioritarias pendientes
	          )
	or
		(	e1.ultimaActualizacion in Prioritaria   -- la ultima actualizacion es prioritaia
		)
	) and  
	// poscondiciones
	 (some a: (e1.actualizacionesPendientes) |
			e2.actualizacionesPendientes = e1.actualizacionesPendientes - a  and
			e2.ultimaActualizacion= a
}

pred aplicarActualizacionPrioritaria[e1,e2: Estado] {
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

*/
