/*
Considere la siguiente situación:

Los siete miembros del directorio de la empresa Vizcacha S.A. asistieron a la reunión
mensual de directorio, llevada a cabo alrededor de una mesa redonda. Cada uno de los 
miembros del directorio posee una caracteristica que lo distingue del resto, y a menudo se 
nombran haciendo referencia a dicha caracteristica en lugar de llamarse por su apellido.
Luego de la ultima reunion del directorio apareció una polémica leyenda escrita en la 
mesa, en uno de los lugares ocupados por un miembro del directorio. Segun le informaron 
al Sr. Ramirez, presidente de la empresa, la leyenda se encuentra ubicada en el sitio en 
el que se sento el Sr. Guzmán durante la reunión. Sin embargo, antes de tomar acciones 
al respecto, el presidente desea averiguar quiénes eran los vecinos inmediatos del Sr. 
Guzmán para entrevistar a los tres sospechosos. Para ello, en primera medida el presidente
habló con todos los miembros del directorio, destacándose los siguientes fragmentos de 
las conversaciones mantenidas:
*/

/*
NOTA IMPORTANTE:
Cuando se modelan las restricciones basandose en el enunciado, TENER CUIDADO con "separar" las restricciones.
Por ejemplo, en el segundo diálogo que termina con "- comentó el señor Drago", se mencionan dos cosas acerca de los vecinos de Drago,
sin embargo, en un primer intento, quise modelar estas dos cosas por separado. Esto provocó que al terminar de escribir el modelo, no logre
obtener una única instancia, sino dos o incluso tres. El problema era que se formaban mesas redondas de 3 personas, cuando debería ser una
mesa sola de 7. Esto lo solucioné juntando la información que me brinda dicho diálogo en un solo fact. De esta manera, el analizador cuenta con
más información para restringir las combinaciones de las instancias, ya que de la otra forma, se daba lugar a que se produzcan estas 
situaciones "circulares", que paradójicamente, seguían cumpliendo las restricciones del enunciado.


Pasé de esto:

//El canoso se sentó a la izquierda de Drago
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Canoso) and
	(m2 = Drago) and
	(m1 = m2.vecinoIzquierda)
}

//El canoso tenia a un miembro con peluquin a su lado 
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Canoso) and
	(m2.caracteristica = Peluca) and
	(m2 in m1.vecinos)
}

A esto:

fact {one disj m1, m2, m3: Miembro |
	(m1.caracteristica = Canoso) and
	(m2 = Drago) and
	(m3.caracteristica = Peluca) and
	(m1 = m2.vecinoIzquierda) and
	(m3 in m1.vecinos)
}

donde junto las dos restricciones anteriores en una sola.
*/


abstract sig Miembro {
	caracteristica: one Caracteristica,
	vecinos: some Miembro,
	vecinoIzquierda: one Miembro,
	vecinoDerecha: one Miembro
}

abstract sig Caracteristica {}

one sig Camacho, Drago, Figueroa, Estevez, Aguirre, Baez, Guzman extends Miembro {}

one sig Anteojos, Canoso, Peluca, Pipa, Monyito, Reloj, Bigote extends Caracteristica {}

---- Restricciones Generales ----

//Hay 7 miembros
fact {#Miembro = 7}



//Cada miembro tiene una caracteristica distinta
fact {all disj m1, m2: Miembro | (m1.caracteristica != m2.caracteristica)}

//Los vecinos de un miembro son el que se sentó a su izquierda y el que se sentó a su derecha
fact {all m: Miembro | (m.vecinos = m.vecinoIzquierda + m.vecinoDerecha)}

//Un miembro no puede tenerse a si mismo de vecino
fact {all m: Miembro | (m not in m.vecinos)}

//Cada miembro tiene un vecino distinto a su derecha y a su izquierda
fact {all disj m1, m2: Miembro | (m1.vecinoIzquierda != m2.vecinoIzquierda)}
fact {all disj m1, m2: Miembro | (m1.vecinoDerecha != m2.vecinoDerecha)}

//Si un miembro tiene un cierto vecino a su izquierda, éste último debe tener a ese miembro a su derecha
fact {all disj m1, m2: Miembro | 
	((m2 = m1.vecinoIzquierda) implies (m1 = m2.vecinoDerecha)) and
	((m2 = m1.vecinoDerecha) implies (m1 = m2.vecinoIzquierda))
}

//Si un miembro tiene un cierto vecino a su izquierda, no puede tenerlo a su derecha, y viceversa
fact {all disj m1, m2: Miembro |
	((m2 = m1.vecinoIzquierda) implies (m2 != m1.vecinoDerecha)) and
	((m2 = m1.vecinoDerecha) implies (m2 != m1.vecinoIzquierda))
}

//Si un miembro no es vecino de otro, este otro tampoco 
fact {all disj m1, m2: Miembro |
	((m2 not in m1.vecinos) implies (m1 not in m2.vecinos))
}

//El conjunto de vecinos de un miembro no puede coincidir con el de otro miembro
fact {all disj m1, m2: Miembro |
	(m1.vecinos != m2.vecinos)
}

---- Restricciones particulares ----

//Camacho se sentó al lado del que usa anteojos
fact {one disj m1, m2: Miembro |
	(m1 = Camacho) and 
	(m2.caracteristica = Anteojos) and 
	(m1 in m2.vecinos)
}

//El canoso se sentó a la izquierda de Drago, y tenia un miembro con peluquin a su lado
fact {one disj m1, m2, m3: Miembro |
	(m1.caracteristica = Canoso) and
	(m2 = Drago) and
	(m3.caracteristica = Peluca) and
	(m1 = m2.vecinoIzquierda) and
	(m3 in m1.vecinos)
}

//Alguien con pipa se sentó a la derecha de Figueroa
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Pipa) and
	(m2 = Figueroa) and
	(m1 = m2.vecinoDerecha)
}

//Drago estaba al lado de quien estaba a la izquierda de Figueroa
fact {one disj m1, m2, m3: Miembro |
	(m1 = Drago) and
	(m3 = Figueroa) and
	(m1 in m2.vecinos) and
	(m2 = m3.vecinoIzquierda)
}

//El vecino del que estaba a la izquierda del miembro que posee bigote, era Estevez
fact {one disj m1, m2, m3: Miembro |
	(m1 = Estevez) and
	(m3.caracteristica = Bigote) and
	(m1 in m2.vecinos) and
	(m2 = m3.vecinoIzquierda)
}

//El que usa moño está a la derecha del de bigote
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Monyito) and
	(m2.caracteristica = Bigote) and
	(m1 = m2.vecinoDerecha)
}

//El que tiene un reloj de oro se sentó a la derecha de Aguirre
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Reloj) and
	(m2 = Aguirre) and
	(m1 = m2.vecinoDerecha)
}

//Baez estaba a la derecha del que posee reloj
fact {one disj m1, m2: Miembro |
	(m1.caracteristica = Reloj) and
	(m2 = Baez) and
	(m1.vecinoDerecha = m2)
}

run {} for 7 Miembro, 5 Int
