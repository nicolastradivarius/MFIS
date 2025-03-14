/* Sincronizacion de archivos en la nube

Modelo para un solo archivo */

open util/ordering[Estado] as ord

sig Archivo { }

sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

sig Estado {
	// agregamos un campo de archivo para poder trackear los archivos y sus actualizaciones
	archivo: some Archivo,
	actualizacionesPendientes: set Actualizacion,
	ultimaActualizacion: lone Actualizacion 
}

// con este hecho se asegura que en cada estado se trackeen todos los archivos existentes.
fact {
	all e: Estado | #(e.archivo) = #Archivo
}
	
// minima cantidad de solicitudes \\
fact { #Actualizacion > 2 and #Prioritaria > 0 } 

// definicion de estado válido
fact {
	all e:Estado | 
		(e.actualizacionesPendientes & e.ultimaActualizacion) = none or
		(e.actualizacionesPendientes + e.ultimaActualizacion) = none
} 


/**
Muestre las modificaciones que sería necesario efectuar en el modelo, estático, para considerar la 
existencia de dos átomos de la signatura Archivo. ¿Cómo se deberían generalizar los cambios para considerar 
cualquier cantidad de átomos de la signatura Archivo? Muestre ambas definiciones en un mismo archivo .als.

Respuesta: la multiplicidad de la signatura Archivo deberia ser borrada y que por defecto sea `set`.
Luego, un fact para restringir la cantidad de átomos de Archivo a 2.
Si se quiere cualquier cantidad de átomos, borrar el fact.
*/

fact dosArchivos {
	#Archivo = 2
}


run default {} for 9

// El analizador ahora no encuentra contraejemplos.
check soloUnaUltimaActualizacion {
	all e: Estado | #(e.ultimaActualizacion) <= 1
} for 15

// El analizador sigue sin encontrar contraejemplos.
check noActualizacionPendienteYUltima {
	all e: Estado | no a: Actualizacion | a in e.actualizacionesPendientes and a in e.ultimaActualizacion
} for 15


