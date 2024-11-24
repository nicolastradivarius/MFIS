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
