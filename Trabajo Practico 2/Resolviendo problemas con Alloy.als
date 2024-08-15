sig Guerrero {
	nombre: one Nombre,
	experto: one Arma,
	ciudad: one Ciudad,
	aporto: one Porcentaje
}

abstract sig Nombre {}

abstract sig Arma {}

abstract sig Ciudad {}

abstract sig Porcentaje {}

//Con "one" digo que son signaturas "singleton", o sea, que sólo tienen un átomo
one sig Sargon, UrEl, Hattusil extends Nombre {}

one sig Espada, Hacha, Lanza extends Arma {}

one sig Elam, Akkad, Hatti extends Ciudad {}

//Treinticinco existe por inferencia, sólo porque sé que existen los otros dos, y entre los tres suman el 100%
one sig Cuarenta, Treinticinco, Veinticinco extends Porcentaje {}


---- Restricciones Generales ----

//Existen exactamente tres Guerreros
fact {#Guerrero = 3}

//No puede haber guerreros con el mismo nombre
fact {no disj g1, g2: Guerrero | g1.nombre = g2.nombre}
//Uso la igualdad de conjuntos porque sé que el conjunto resultante del join va a tener un solo elemento
//ya que la relación "nombre" es uno a uno

//No hay dos guerreros que provengan de la misma ciudad
fact {no disj g1, g2: Guerrero | g1.ciudad = g2.ciudad}

//No hay dos guerreros que sean expertos con la misma arma
fact {all disj g1, g2: Guerrero | g1.experto != g2.experto}

//No hay dos guerreros distintos que hayan aportado el mismo valor al ejercito
fact {all g1, g2: Guerrero | (g1 != g2) implies (g1.aporto != g2.aporto)}
//Este hecho lo puedo modelar de esta forma porque la relacion "aporto" es uno a uno,
//entonces no va a suceder que un mismo guerrero tenga dos porcentajes distintos (si sucediera, no lo
//estaría contemplando con este hecho, lo estaría pasando por alto).

---- Restricciones particulares ----

//UrEl no es de Hatti: existe un guerrero que se llama UrEl y no proviene de Hatti
fact {one g: Guerrero | (g.nombre = UrEl) and (g.ciudad != Hatti)}

//El guerrero que menos porcentaje aportó es un experto con la lanza.
//No especifica cuál es ese porcentaje, sólo dice que es el menor que un guerrero aportó.
fact {one g: Guerrero | (aportoMenorPorc[g]) and (g.experto = Lanza)}

//Sargon aportó un porcentaje mayor que el guerrero de Elam
fact {one disj g1, g2: Guerrero | (g1.nombre = Sargon) and (g2.ciudad = Elam) and (aportoMayorPorc[g1, g2])}

//Hattusil no fue el que aportó el 40%, es experto con el hacha
fact {one g: Guerrero | (g.nombre = Hattusil) and (g.aporto != Cuarenta) and (g.experto = Hacha)}

//El guerrero de Akkad es un experto con la espada
fact {one g: Guerrero | (g.ciudad = Akkad) and (g.experto = Espada)}

---- Predicados ----

//Verdadero si g es el guerrero que aportó el menor porcentaje de los existentes, en este caso, 25
pred aportoMenorPorc[g: Guerrero] {
	(g.aporto = Veinticinco)
}

pred aportoMayorPorc[g1, g2: Guerrero] {
	//Primer caso: g1 aportó 40% y g2 aportó uno de los porcentajes menores
	((g1.aporto = Cuarenta) and ((g2.aporto = Treinticinco) or (g2.aporto = Veinticinco))) or
	//Segundo caso: g1 aportó 35% y g2 tiene que aportar 25% que es el único porcentaje menor que queda.
	((g1.aporto = Treinticinco) and (g2.aporto = Veinticinco))
}

run {}
