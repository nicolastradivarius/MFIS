/*
Considere la siguiente situacion:
En los ultimos cuatro meses (de Julio a Octubre) Pedro trabajo en cuatro empresas distintas:
tres de ellas europeas y otra brasilera. Siempre trabajo dentro del area administrativa,
y en cada empresa desempeño funciones en una seccion diferente. 
En un momento de melancolia Pedro reconocio que el trabajo que mas le gusto fue el realizado en 
la seccion de Ventas, a pesar de las altas exigencias de su jefe. Ademas, Pedro recuerda lo siguiente:
*/

abstract sig Empresa {
	mes: one Mes,
	nacionalidad: one Nacionalidad,
	seccion: one Seccion 
}

abstract sig Mes {
	previos: set Mes
}

abstract sig Nacionalidad {}

sig Europea in Nacionalidad {}

abstract sig Seccion {}

one sig Sky, Nexos, Alpha, Titaz extends Empresa {}

one sig Julio, Agosto, Septiembre, Octubre extends Mes {}

one sig Italiana, Francesa, Polaca, Brasilera extends Nacionalidad {}

one sig Recepcion, Ventas, Cobranzas, Compras extends Seccion {}

---- Restricciones generales ----

//definimos los meses previos para los meses del modelo
fact {one m: Mes | (m = Julio) and (m.previos = none)}
fact {one m: Mes | (m = Agosto) and (m.previos = Julio.previos + Julio)}
fact {one m: Mes | (m = Septiembre) and (m.previos = Agosto.previos + Agosto)}
fact {one m: Mes | (m = Octubre) and (m.previos = Septiembre.previos + Septiembre)}

//hay exactamente cuatro empresas
fact {#Empresa = 4}

//las nacionalidades italiana, polaca y francesa son europeas
fact {Italiana + Francesa + Polaca = Europea}

//Pedro trabajó en un área distinta para cada empresa
fact {no disj e1, e2: Empresa | (e1.seccion = e2.seccion)}

//Pedro trabajó en empresas de diferente nacionalidad
fact {all disj e1, e2: Empresa | (e1.nacionalidad != e2.nacionalidad)}

//Pedro trabajó en una empresa diferente cada mes
fact {all e1, e2: Empresa | (e1 != e2) implies (e1.mes != e2.mes)}

---- Restricciones Particulares ----

//El trabajo de Pedro en Sky fue previo al de Nexos
fact {one disj e1, e2: Empresa |
	(e1 = Sky) and
	(e2 = Nexos) and
	(e1.mes in e2.mes.previos)
}

//En Septiembre, Pedro trabajó en Recepción en una empresa
fact {one e: Empresa | (e.seccion = Recepcion) and (e.mes = Septiembre)}

//Su primer trabajo fue en la sección de Compras de una empresa italiana.
//como dice "primer trabajo" se infiere que fue en el primer mes de los cuatro meses
//pero esto no se puede poner directamente en el hecho. Se delega en un predicado
fact {one e: Empresa | (e.seccion = Compras) and (e.nacionalidad = Italiana) and esPrimerTrabajo[e]}

//En Alpha trabajó dos meses despues de ingresar en una empresa europea en la que trabajó en Cobranzas
fact {one disj e1, e2: Empresa | 
	(e1 = Alpha) and 
	esDosMesesPrevios[e2.mes, e1.mes] and
	(e2.nacionalidad in Europea) and
	(e2.seccion = Cobranzas)
}

//En Titaz trabajó antes que en una empresa francesa 
fact {one disj e1, e2: Empresa | (e1 = Titaz) and (e2.nacionalidad = Francesa) and (e1.mes in e2.mes.previos)}

//En Titaz trabajó después que en una empresa polaca
fact {one disj e1, e2: Empresa | (e1 = Titaz) and (e2.nacionalidad = Polaca) and (e1.mes !in e2.mes.previos)}

---- Predicados & Funciones ----

//Determina si m1 está dos meses por detrás de m2
pred esDosMesesPrevios [m1, m2: Mes] {
	((m1 = Julio) and (m2 = Septiembre)) or
	((m1 = Agosto) and (m2 = Octubre))
}

//Determina si la empresa "e" corresponde a la empresa donde Pedro inició su aventura por el trabajo.
pred esPrimerTrabajo [e: Empresa] {
	(e.mes = Julio)
}
---- Instancias ----

run SkyDespuesNexos {one disj e1, e2: Empresa | 	
	(e1 = Sky) and
	(e2 = Nexos) and
	(e1.mes = Octubre and e2.mes = Julio)
} for 4

run {} for 4
