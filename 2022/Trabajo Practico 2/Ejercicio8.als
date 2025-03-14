/*
Considere la siguiente situacion:

El rey de Francia organizo una partida de naipes y, mientras jugaban, todos los asistentes 
aprovecharon para ponerse al dia de los ultimos chismes. Luego de un rato, la conversacion
se centró en las parejas que se habían formado en el ultimo baile realizado en Versalles 
la semana pasada. El marques de la Politesse recordaba que se formaron cuatro nuevas 
parejas y que cada una de ellas bailo solo una vez en toda la noche, en diferente horario, y 
una danza distinta (cotillon, minué, forlán y gavota). Se sabe que los bailes se realizaron 
exactamente cada 60 minutos y que la primera pareja en bailar lo hizo a la 1 de la mañana.
Haciendo memoria, la reina mencionó los siguientes datos que surgieron en la conversacion:
*/

sig Pareja {
	bailarin: one Hombre,
	bailarina: one Mujer,
	baile: one Baile,
	horaBaile: one Hora
}

abstract sig Hombre {}

abstract sig Mujer {}

abstract sig Baile {}

abstract sig Hora {
	previos: set Hora
}

one sig Labourd, Calvinet, Tolosa, Perigau extends Hombre {}

one sig Gauttier, Maine, Touraine, Abornou extends Mujer {}

one sig Cotillon, Minue, Forlan, Gavota extends Baile {}

one sig UnaAM, DosAM, TresAM, CuatroAM extends Hora {}

---- Restricciones generales ----

//Hay exactamente cuatro parejas
fact {#Pareja = 4}

//Cada pareja estaba formada por un bailarin y bailarina distintos
fact {all disj p1, p2: Pareja | (p1.bailarin != p2.bailarin) and (p1.bailarina != p2.bailarina)}
//fact {no disj p1, p2: Pareja | (p1.bailarin = p2.bailarin) and (p1.bailarina = p2.bailarina)}
//el fact de arriba está mal porque busca que no sean iguales en simultaneo, cuando deberia ser por separado

//Cada pareja bailó un tipo de baile distinto
fact {no disj p1, p2: Pareja | (p1.baile = p2.baile)}

//Cada pareja bailó a una hora diferente
//fact {all p1, p2: Pareja | (p1 = p2) implies (p1.horaBaile = p2.horaBaile)}
//No sirve porque pasa por alto los casos donde p1 != p2
fact {all p1, p2: Pareja | (p1.horaBaile = p2.horaBaile) implies (p1 = p2)}

//Establecemos las horas previas a cada hora del modelo
fact {one h: Hora | (h = UnaAM) and (h.previos = none)}
fact {one h: Hora | (h = DosAM) and (h.previos = UnaAM.previos + UnaAM)}
fact {one h: Hora | (h = TresAM) and (h.previos = DosAM.previos + DosAM)}
fact {one h: Hora | (h = CuatroAM) and (h.previos = TresAM.previos + TresAM)}

---- Restricciones generales ----

//La baronesa de Gauttier bailó el cotillón o el minué, y no bailó con el marques de Labourd
fact {
	one p: Pareja | 
		(p.bailarina = Gauttier) and 
		(p.baile in (Cotillon + Minue)) and
		(p.bailarin != Labourd)
}

//La marquesa de Maine bailó el forlán con el vizconde Calvinet, quienes NO bailaron a las 4 am
fact {
	one p: Pareja |
		(p.bailarina = Maine) and
		(p.bailarin = Calvinet) and
		(p.baile = Forlan) and
		(p.horaBaile != CuatroAM)
}

//La pareja que bailó el minué lo hizo antes que la pareja que bailó la gavota
fact {
	one disj p1, p2: Pareja |
		(p1.baile = Minue) and
		(p2.baile = Gavota) and
		bailoAntes[p1, p2]
}

//La condesa de Touraine no bailó Cotillón y bailó despues que el marques de Labourd
fact {
	one disj p1, p2: Pareja |
		(p1.bailarina = Touraine) and
		(p1.baile != Cotillon) and
		(p2.bailarin = Labourd) and
		bailoDespues[p1, p2]
}

//El conde de Tolosa no bailó con la condesa de Touraine ni con la duquesa de Abornou
fact {
	one p: Pareja |
		(p.bailarin = Tolosa) and
		(p.bailarina not in Touraine + Abornou)
}

//La condesa de Touraine criticó a una mujer de la pareja que bailó el minué. Una de las dos bailó a la 1AM y otra a las 3
fact {
	one disj p1, p2: Pareja |
		(p1.bailarina = Touraine) and
		(p2.baile = Minue) and
		(p1.horaBaile in (UnaAM + TresAM)) and
		(p2.horaBaile in (UnaAM + TresAM))
//tambien se puede poner ((p1.horaBaile + p2.horaBaile) = (UnaAM + TresAM))
}

---- Predicados & Funciones ----

//Determina que la pareja p1 bailó en una hora previa a la de p2
pred bailoAntes [p1, p2: Pareja] {
	(p1.horaBaile) in (p2.horaBaile.previos)
}

pred bailoDespues [p1, p2: Pareja] {
	bailoAntes[p2, p1]
}

---- Instancias ----

run {} for 4

/*
¿Por qué al ejecutar mismoBailarinDistintaBailarina1, Alloy no encuentra instancias,
pero al ejecutar mismoBailarinDistintaBailarina2, sí encuentra? ¿No se supone que la instancia de
mismoBailarinDistintaBailarina2 es un caso concreto de mismoBailarinDistintaBailarina1? Porque
de hecho, en ambos comandos estamos pidiendo explícitamente dos parejas que tengan
el mismo bailarín pero distinta bailarina, solo que en mismoBailarinDistintaBailarina2 estamos
especificando quiénes son esos bailarines que queremos.

La clave está en la multiplicidad.
En mismoBailarinDistintaBailarina1, estamos pidiendo que haya EXACTAMENTE un par de parejas
que tengan el mismo bailarin y distinta bailarina.
En mismoBailarinDistintaBailarina2 estamos pidiendo que haya EXACTAMENTE un par de parejas
que tengan de bailarin a Sybarite, y de bailarinas a Gauttier y Maine respectivamente.
Cuando ejecutamos mismoBailarinDistintaBailarina2, Alloy encuentra una instancia en la que haya
exactamente un par de parejas así porque logra encontrar una combinación de átomos tal que
se dé esa situación con los respectivos átomos especificados.
En cambio, cuando ejecutamos mismoBailarinDistintaBailarina1, ocurre algo interesante: Alloy no
encuentra instancias donde haya EXACTAMENTE un par de parejas tal que se cumpla esa condición,
porque en realidad, en todas las instancias donde se cumpliría esa condición, hay DOS pares:
el de (p1, p2) y el de (p2, p1). ¿Por qué? Porque si tenemos que (p1, p2) es un par de parejas tal que
el bailarin de p1 es el mismo que el de p2, y la bailarina de p1 es distinta a la de p2, entonces
tranquilamente podemos dar vuelta los roles de p1 y p2 que la condición se va a seguir cumpliendo.
De ahí que haya dos, y no exactamente un par.
A diferencia de en mismoBailarinDistintaBailarina2, el par (p1, p2) era único. Si lo dabamos vuelta,
quedaría como (p2, p1), de manera que (p2.bailarina = Maine y p1.bailarina Gauttier); al contrastar esto
en la condición del run, que dice que la bailarina del 1ro debe ser Gauttier y la del 2do debe ser Maine,
claramente no se cumple, y por eso mismo, el par de parejas producido por dar vuelta el par
original no satisface la condición del run, dejándonos con exactamente un par que sí lo hace.
*/

run mismahora {
	some disj p1, p2: Pareja |
		(p1.horaBaile = p2.horaBaile)
} for 4

run mismoBailarinDistintaBailarina1 {
	one disj p1, p2: Pareja | 
		(p1.bailarin = p2.bailarin) and 
		(p1.bailarina != p2.bailarina)
} for 4

run mismoBailarinDistintaBailarina2 {
	one disj p1, p2: Pareja |
		(p1.bailarin = Labourd) and
		(p2.bailarin = Labourd) and
		(p1.bailarina = Gauttier) and
		(p2.bailarina = Maine)
} for 4


