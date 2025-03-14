/* Sincronizacion de archivos en la nube

Modelo para un solo archivo */

open util/ordering[Estado] as ord

one sig Archivo { }

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

sig Estado {
	actualizacionesPendientes: set Actualizacion,
	// habría que cambiarla a `lone`.
	ultimaActualizacion: some Actualizacion 
}
	
// minima cantidad de solicitudes \\
fact { #Actualizacion > 2 and #Prioritaria > 0 } 

// definicion de estado válido
fact {
	all e:Estado | 
		// no hay una actualizacion pendiente que figure como última.
		(e.actualizacionesPendientes & e.ultimaActualizacion) = none or -- ¿en qué caso podría ser != de none?
		// pareciera que esto cubre el caso donde ambos campos son vacíos, pero la expresión anterior también lo cubre...
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} 

// limitacion de la cantidad de solicitudes marcadas como última \\
// Provoca que el analizador no encuentre instancias porque es una contradicción directa a la multiplicidad
// establecida para el campo `ultimaActualizacion`.
--fact { all e:Estado | #(e.ultimaActualizacion) < 1 }


/**
Evalue si el modelo, estatico, dado en el archivo anexo NubeEstadosEstatico.als es adecuado. 
Deje comentarios sobre los comandos utilizados y los resultados obtenidos/problemas encontrados. 
No modifique el modelo en este inciso.
*/


run default {}

// El significado del campo "ultimaActualización" indicaría que solo puede haber una, o ninguna.
assert soloUnaUltimaActualizacion {
	all e: Estado | lone e.ultimaActualizacion
		
}

// El analizador encuentra contraejemplos porque la multiplicidad de esta relacion es `some`.
check soloUnaUltimaActualizacion

// Chequeamos que nunca una actualización pueda estar pendiente y ser la última al mismo tiempo.
// Según la descripción de la operación LlegaActualización, y la definición de estado válido, esto no debería ser posible.
// No encuentra contraejemplos.
check noActualizacionPendienteYUltima {
	all e: Estado | no a: Actualizacion | a in e.actualizacionesPendientes and a in e.ultimaActualizacion
} for 15

// testing para ver si existe un caso donde se satisfaga el fact de estado válido con (F or V).
run $1 {
	some e:Estado | 
		(e.actualizacionesPendientes & e.ultimaActualizacion) != none and
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} for 40
