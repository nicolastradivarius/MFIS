/*
Hay 5 casas que poseen distinto color, y se encuentran consecutivamente en la misma
vereda, identificadas en las posiciones A, B, C, D y E. En particular, se considera que 
la casa B esta a la derecha de la casa A (respectivamente, la casa A se encuentra a la 
izquierda de la casa B), la casa C se encuentra a la derecha de la casa B (respectivamente, 
la casa B se encuentra a la izquierda de la casa C), etc. En cada casa vive una persona 
de diferente nacionalidad. Cada uno de los 5 dueños bebe un cierto tipo de bebida, fuma 
una determinada marca de cigarrillos, y posee un tipo de mascota (siendo todos ellos 
distintos entre sí). Asimismo, por ejemplo, las personas que viven en las casas A y C son 
considerados vecinos inmediatos de la persona que vive en la casa B.
*/

sig Casa {
	color: one Color,
	posicion: one Posicion,
	propietario: one Propietario
}

abstract sig Color {}

abstract sig Posicion {}

sig Propietario {
	nacionalidad: one Nacionalidad,
	bebida: one Bebida,
	fuma: one MarcaCigarrillo,
	mascota: one Mascota
}

abstract sig Nacionalidad {}

abstract sig Bebida {}

abstract sig MarcaCigarrillo {}

abstract sig Mascota {}

one sig Rojo, Verde, Blanca, Amarilla, Azul extends Color {}

one sig A, B, C, D, E extends Posicion {}

one sig Britanico, Sueco, Danes, Noruego, Aleman extends Nacionalidad {}

one sig Te, Cafe, Leche, Cerveza, Agua extends Bebida {}

one sig PallMall, Dunhill, Blends, BlueMaster, Prince extends MarcaCigarrillo {}

one sig Perro, Pajaro, Gato, Caballo, Pez extends Mascota {}

---- Restricciones Generales ----

//Hay exactamente 5 casas, donde vive una persona en cada una
fact {#Casa = 5}

fact {#Propietario = 5}

//Cada casa tiene un color diferente, está posicionada en un lugar diferente y tiene un propietario diferente
/*
fact {no disj c1, c2: Casa | (c1.color = c2.color) and (c1.posicion = c2.posicion) and (c1.propietario = c2.propietario)}
Esto no me sirve porque está evaluando que no haya dos casas que incumplan esta condicion "en conjunto".
Por ejemplo, si c1 es Azul, está en E y su propietario es Propietario4, y c2 es Azul, está en D y su propietario es el mismo, 
efectivamente se está cumpliendo que c1 y c2 no compartan "color, posicion Y propietario" ya que la posicion no la comparten.
Una forma de verlo es la siguiente: dadas dos casas c1 y c2 con las propiedades anteriores:
	- Su color es el mismo? True
	- Su posicion es la misma? False
	- Su propietario es el mismo? True
True AND False AND True = False. Como hay un "no" al inicio, es "no false", o sea, se niega el false, y se vuelve True, haciendo que el hecho se valide.
Entonces tengo dos opciones:
	- debo evaluar las condiciones por separado, para garantizar que cada miembro de la relacion sea evaluado, y no en conjunto
	- puedo evaluar las condiciones en conjunto siempre y cuando diga que para todo par de atomos disjuntos, dichas propiedades son distintas en uno y en el otro, i.e:
	fact {all disj c1, c2: Casa | (c1.color != c2.color) and (c1.posicion != c2.posicion) and (c1.propietario != c2.propietario)}
*/
fact {no disj c1, c2: Casa | (c1.color = c2.color)}
fact {no disj c1, c2: Casa | (c1.posicion = c2.posicion)}
fact {no disj c1, c2: Casa | (c1.propietario = c2.propietario)}

// En cada casa vive una persona de diferente nacionalidad
fact {all disj p1, p2: Propietario | (p1.nacionalidad != p2.nacionalidad)}

// Cada uno de los 5 dueños bebe un cierto tipo de bebida
fact {all disj p1, p2: Propietario | (p1.bebida != p2.bebida)}

//Cada uno de los 5 dueños fuma una determinada marca de cigarrillos
fact {all disj p1, p2: Propietario | (p1.fuma != p2.fuma)}

//Cada uno de los 5 dueños posee un tipo de mascota
fact {all disj p1, p2: Propietario | (p1.mascota != p2.mascota)}


---- Restricciones Particulares ----

//El britanico vive en la casa roja
fact {one c: Casa | (c.propietario.nacionalidad = Britanico) and (c.color = Rojo)}

//El sueco posee perros
fact {one p: Propietario | (p.nacionalidad = Sueco) and (p.mascota = Perro)}

//El danes bebe té
fact {one p: Propietario | (p.nacionalidad = Danes) and (p.bebida = Te)}

//La casa verde esta a la izquierda de la casa blanca.
fact {one disj c1, c2: Casa | 
	(c1.color = Verde) and 
	(c2.color = Blanca) and 
	estaIzquierda[c1, c2]
}

//El dueño de la casa verde bebe cafe
fact {one c: Casa | (c.color = Verde) and (c.propietario.bebida = Cafe)}

//La persona que fuma PallMall posee Pajaros
fact {one p: Propietario | (p.fuma = PallMall) and (p.mascota = Pajaro)}

//El dueño de la casa amarilla fuma Dunhill
fact {one c: Casa | (c.color = Amarilla) and (c.propietario.fuma = Dunhill)}

//El dueño de la casa del centro bebe leche
fact {one c: Casa | estaCentro[c] and (c.propietario.bebida = Leche)}

//El noruego vive en la casa A
fact {one c: Casa | (c.propietario.nacionalidad = Noruego) and (c.posicion = A)}

//La persona que fuma Blends es vecina inmediata de la persona que posee gatos
fact {one disj c1, c2: Casa | 
	(c1.propietario.fuma = Blends) and 
	(c2.propietario.mascota = Gato) and
	esVecinoInmediato[c1, c2]
}

//La persona que posee Caballos es vecina inmediata del que fuma Dunhill
fact {one disj c1, c2: Casa | 
	(c1.propietario.mascota = Caballo) and
	(c2.propietario.fuma = Dunhill) and
	esVecinoInmediato[c1, c2]
}

//La persona que fuma BlueMaster bebe cerveza
fact {one p: Propietario | (p.fuma = BlueMaster) and (p.bebida = Cerveza)}

//El aleman fuma Prince
fact {one p: Propietario | (p.nacionalidad = Aleman) and (p.fuma = Prince)}

//El noruego es vecino inmediato del que vive en la casa azul
fact {one disj c1, c2: Casa | 
	(c1.propietario.nacionalidad = Noruego) and
	(c2.color = Azul) and
	esVecinoInmediato[c1, c2]
}

//La persona que fuma Blend es vecina inmediata de la persona que bebe agua
fact {one disj c1, c2: Casa | 
	(c1.propietario.fuma = Blends) and 
	(c2.propietario.bebida = Agua) and
	esVecinoInmediato[c1, c2]
}

---- Predicados & Funciones----

//Determina que la casa c1 está a la izquierda de la casa c2
//no puedo usar "implies" porque no cubro todos los casos, salvo que incluya la ultima linea (la de E)
pred estaIzquierda [c1, c2: Casa] {
	((c1.posicion = A) implies (c2.posicion = B)) and
	((c1.posicion = B) implies (c2.posicion = C)) and
	((c1.posicion = C) implies (c2.posicion = D)) and
	((c1.posicion = D) implies (c2.posicion = E)) and
	((c1.posicion = E) implies (c2.posicion = none))
}

//Determina que la casa c está en el centro
pred estaCentro [c: Casa] {
	(c.posicion = C)
}

//Determina que c1 es vecino inmediato de c2. Esto significa que c1 está a la izquierda ó derecha de c2
//Como la relacion posicion es muchos a uno (muchas casas están vinculadas a una posicion), entonces
//no puede suceder que c1 este a la izquierda Y a la derecha de c2 porque eso implicaria que c1 no esta
//vinculado exactamente a una posicion
pred esVecinoInmediato [c1, c2: Casa] {
	estaIzquierda[c1, c2] or
	estaDerecha[c1, c2]
}

pred estaDerecha [c1, c2: Casa] {
	estaIzquierda[c2, c1]
}

---- Instancias ----

run mismacasadosposiciones {one c: Casa | (c.posicion = A) and (c.posicion = B)}

run {} for 5

//Quién posee peces como mascota? 
run peces {one p: Propietario | (p.mascota = Pez)} for 5
//El de la casa color verde, posición D, un aleman quien bebe café y fuma Prince

