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
Corrija los errores detectados en el inciso anterior y verifique que el modelo sea correcto estáticamente. 
Puede modificar el modelo, agregar, eliminar y corregir facts según un considere necesario.
Deje expresado en comentarios lo modificado justificando los cambios realizados 
(haga mención al comentario del punto anterior que da lugar a la situación).
*/


run default {}

// El analizador ahora no encuentra contraejemplos.
check soloUnaUltimaActualizacion {
	all e: Estado | #(e.ultimaActualizacion) <= 1
} for 15

// El analizador sigue sin encontrar contraejemplos.
check noActualizacionPendienteYUltima {
	all e: Estado | no a: Actualizacion | a in e.actualizacionesPendientes and a in e.ultimaActualizacion
} for 15


