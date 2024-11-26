/**
Los repositorios en la nube traen aparejados algunos problemas de sincronización sobre la información almacenada en ellos.
Considere el repositorio “ProximaNube”. El repositorio lleva un registro de los pedidos de actualización que vayan
llegando.

Considere ahora el modelo dado en el anexo 2, pensado para modelar la dinámica del escenario planteado a través 
de la noción de estado. En este caso, asuma que el repositorio tiene como política de sincronización permitirle
el acceso a la última solicitud de actualización, a menos que solo haya una única solicitud de actualización 
pendiente o haya alguna solicitud identificada como prioritaria. Tenga en cuenta que las únicas acciones posibles 
para establecer cambios de estado son las siguientes:

**Llegada de una solicitud de actualización:** Al llegar una solicitud de actualización, la misma debe registrarse
en la relación `ultimaActualizacion`. En caso de que haya una solicitud previa en dicha relación, la solicitud 
previa debe moverse a `actualizacionesPendientes`.

**Aplicación de la última solicitud de actualización:** Es posible realizar la operación `AplicarUltimaActualizacion` 
si la solicitud almacenada en la relación `ultimaActualizacion` es prioritaria, o bien si no lo es pero no hay 
actualizaciones prioritarias pendientes. En caso de que la actualización aplicada sea prioritaria, se eliminan 
todas las actualizaciones pendientes. En caso de que la actualización aplicada no sea prioritaria, se coloca como 
`ultimaActualizacion` alguna de las actualizaciones que estaban pendientes.

**Aplicación de una solicitud de actualización prioritaria:** La operación `AplicarActualizacionPrioritaria` 
efectúa una actualización prioritaria que se encuentre pendiente. Al aplicarla, se deben eliminar todas las 
actualizaciones que estaban pendientes al momento de registrar en la relación `ultimaActualizacion` la actualización 
aplicada.

*/

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
