/*
Considerar la siguiente situación:
El Primero de Enero de este año, luego del brindis de año nuevo, cinco parejas amigas se 
reunieron para festejar. Los apellidos de las parejas son Jonas, Palacio, Rodriguez, Garcia 
y Saravia. Por otra parte, los nombres de pila de las esposas son Elsa, Juana, Marcia, 
Elizabeth y Carla. Asimismo, los nombres de los esposos son Rodolfo, Daniel, Carlos, 
Pedro y Miguel. Entre otras cosas, charlaron acerca del mes del año en que cada pareja 
celebra su aniversario, siendo cada uno de ellos en un mes distinto: Febrero, Abril, Agosto, 
Septiembre y Octubre. Durante la velada, se expuso la siguiente información:

(se omite y se procede directo a la definición del modelo)
*/

sig Pareja {
	apellido: one Apellido,
	nombreEsposa: one NombreEsposa,
	nombreEsposo: one NombreEsposo,
	aniversario: one Mes
}

abstract sig Apellido {}

abstract sig NombreEsposa {}

abstract sig NombreEsposo {}

abstract sig Mes {
	mesesPrevios: set Mes
}

one sig Jonas, Palacio, Rodriguez, Garcia, Saravia extends Apellido {}

one sig Elsa, Juana, Marcia, Elizabeth, Carla extends NombreEsposa {}

one sig Rodolfo, Daniel, Carlos, Pedro, Miguel extends NombreEsposo {}

one sig Febrero, Abril, Agosto, Septiembre, Octubre, Diciembre extends Mes {}

---- Restricciones Generales ----

//Hay exactamente cinco parejas
fact {#Pareja = 5}

//Cada pareja tiene un apellido, un nombre de Esposa, de Esposo y aniversarios diferentes.
fact {all disj p1, p2: Pareja |
	(p1.apellido != p2.apellido) and
	(p1.nombreEsposa != p2.nombreEsposa) and
	(p1.nombreEsposo != p2.nombreEsposo) and
	(p1.aniversario != p2.aniversario)
}

//Diciembre no es un mes de aniversario de alguna de las parejas
fact {all p: Pareja | (p.aniversario != Diciembre)}

//Cada mes tiene sus meses previos correspondientes en el contexto del problema.
fact {one m: Mes | (m = Febrero) and (m.mesesPrevios = none)}
fact {one m: Mes | (m = Abril) and (m.mesesPrevios = Febrero.mesesPrevios + Febrero)}
fact {one m: Mes | (m = Agosto) and (m.mesesPrevios = Abril.mesesPrevios + Abril)}
fact {one m: Mes | (m = Septiembre) and (m.mesesPrevios = Agosto.mesesPrevios + Agosto)}
fact {one m: Mes | (m = Octubre) and (m.mesesPrevios = Septiembre.mesesPrevios + Septiembre)}
fact {one m: Mes | (m = Diciembre) and (m.mesesPrevios = Octubre.mesesPrevios + Octubre)}

---- Restricciones Particulares ----

//Juana celebra su aniversario antes que Carlos y los Palacio
fact {one disj p1, p2, p3: Pareja | 
	(p1.nombreEsposa = Juana) and
	(p2.nombreEsposo = Carlos) and
	(p3.apellido = Palacio) and
	esMesPrevio[p1.aniversario, p2.aniversario] and
	esMesPrevio[p1.aniversario, p3.aniversario]
}

//Juana celebra su aniversario después que Daniel y los Jonas
fact {one disj p1, p2, p3: Pareja | 
	(p1.nombreEsposa = Juana) and
	(p2.nombreEsposo = Daniel) and
	(p3.apellido = Jonas) and
	!esMesPrevio[p1.aniversario, p2.aniversario] and
	!esMesPrevio[p1.aniversario, p3.aniversario]
}

//Elizabeth celebra su aniversario dos meses después que los Rodriguez
fact {one disj p1, p2: Pareja |
	(p1.nombreEsposa = Elizabeth) and
	(p2.apellido = Rodriguez) and
	esDosMesesAntes[p2.aniversario, p1.aniversario]
}

//Elizabeth celebra su aniversario cuatro meses antes que Rodolfo
fact {one disj p1, p2: Pareja |
	(p1.nombreEsposa = Elizabeth) and
	(p2.nombreEsposo = Rodolfo) and
	esCuatroMesesAntes[p1.aniversario, p2.aniversario]
}

//El hijo de Marcia cumple años en Diciembre, dos meses después del aniversario de sus padres
//Es posible que esta restriccion no sea necesaria modelarla.

//Los Saravia celebran su aniversario cuatro meses después que Pedro
fact {one disj p1, p2: Pareja | 
	(p1.apellido = Saravia) and 
	(p2.nombreEsposo = Pedro) and 
	esCuatroMesesAntes[p2.aniversario, p1.aniversario]
}

//Los Saravia celebran su aniversario dos meses antes que Marcia
fact {one disj p1, p2: Pareja | 
	(p1.apellido = Saravia) and 
	(p2.nombreEsposa = Marcia) and 
	esDosMesesAntes[p1.aniversario, p2.aniversario]
}

//Daniel y Carla celebran primero su aniversario (ocho meses antes que los Garcia)
fact {one disj p1, p2: Pareja |
	(p1.nombreEsposo = Daniel) and
	(p1.nombreEsposa = Carla) and
	(p2.apellido = Garcia) and
	esOchoMesesAntes[p1.aniversario, p2.aniversario]
}

//Miguel celebra su aniversario en Septiembre
fact {one p: Pareja | (p.nombreEsposo = Miguel) and (p.aniversario = Septiembre)}

---- Predicados & Funciones ----



//Determina si la pareja p1 celebra antes su aniversario que la pareja p2
pred esMesPrevio [m1, m2: Mes] {
	(m1 in (m2.mesesPrevios - m2))
}

//Determina si la pareja p1 tiene su aniversario dos meses despues que la pareja p2
pred esDosMesesAntes [m1, m2: Mes] {
	((m1 = Febrero) and (m2 = Abril)) or
	((m1 = Agosto) and (m2 = Octubre))
}

//Determina si el mes m1 está 4 meses por detrás de m2 en el calendario gregoriano (en este modelo)
pred esCuatroMesesAntes [m1, m2: Mes] {
	(m1 = Abril) and (m2 = Agosto)
}

pred esOchoMesesAntes [m1, m2: Mes] {
//	some disj m3, m4: Mes | esDosMesesAntes[m1, m3] and esDosMesesAntes[m3, m4] and esDosMesesAntes[m4, m2]
//no funciona
	(m1 = Febrero) and (m2 = Octubre)
}




---- Instancias ----

assert danielcarla {one disj p1, p2: Pareja |
	(p1.nombreEsposo = Daniel) and
	(p1.nombreEsposa = Carla) and
	(p2.apellido = Garcia) and
	(p1.aniversario = Febrero) and
	(p2.aniversario = Octubre)
}

check danielcarla for 5

//Forza una instancia en la que Juana celebre su aniversario antes/despues/en el mismo mes que otras parejas
run juanaCelebra {
	one disj p1, p2: Pareja | 
		(p1.nombreEsposa = Juana) and 
		(p2.apellido = Palacio) and 
		(p1.aniversario = Agosto) and 
		(p2.aniversario = Septiembre)
} for 5

//Ídem con Elizabeth
run elizabethCelebra {
	one disj p1, p2: Pareja | 
		(p1.nombreEsposa = Elizabeth) and 
		(p2.apellido = Rodriguez) and 
		(p1.aniversario = Octubre) and 
		(p2.aniversario = Agosto)
} for 5

run {} for 5

/*
Respuesta: las parejas están conformadas como sigue:
	- Pareja 1: Garcia, Marcia, Carlos y Octubre
	- Parej


*/
