some sig Pareja {
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

one sig Febrero, Abril, Agosto, Septiembre, Octubre extends Mes {}

// restriccion de orden sobre los meses
fact {one m: Mes | (m = Febrero) and (m.mesesPrevios = none)}
fact {one m: Mes | (m = Abril) and (m.mesesPrevios = Febrero.mesesPrevios + Febrero)}
fact {one m: Mes | (m = Agosto) and (m.mesesPrevios = Abril.mesesPrevios + Abril)}
fact {one m: Mes | (m = Septiembre) and (m.mesesPrevios = Agosto.mesesPrevios + Agosto)}
fact {one m: Mes | (m = Octubre) and (m.mesesPrevios = Septiembre.mesesPrevios + Septiembre)}

fact "hay exactamente cinco parejas" {
	#Pareja = 5
}

fact "no hay dos parejas con las mismas caracteristicas" {
	all disj p1, p2: Pareja | 
		(p1.apellido != p2.apellido) and
		(p1.nombreEsposa != p2.nombreEsposa) and
		(p1.nombreEsposo != p2.nombreEsposo) and
		(p1.aniversario != p2.aniversario)
}

run default {} for 5

fact "Juana celebra su aniversario antes que Carlos y los Palacio" {
	some disj p1, p2, p3: Pareja |
		(p1.nombreEsposa = Juana) and
		(p2.nombreEsposo = Carlos) and
		(p3.apellido = Palacio) and
		(p1.aniversario in p2.aniversario.mesesPrevios) and
		(p1.aniversario in p3.aniversario.mesesPrevios)
}

fact "Juana celebra su aniversario despues que Daniel y los Jonas" {
	some disj p1, p2, p3: Pareja |
		(p1.nombreEsposa = Juana) and
		(p2.nombreEsposo = Daniel) and
		(p3.apellido = Jonas) and
		(p1.aniversario not in p2.aniversario.mesesPrevios) and
		(p1.aniversario not in p3.aniversario.mesesPrevios)
}

fact "Elizabeth celebra su aniversario dos meses despues que los Rodriguez" {
	some disj p1, p2: Pareja |
		(p1.nombreEsposa = Elizabeth) and
		(p2.apellido = Rodriguez) and
		aniversarioDosMesesAntes[p2.aniversario, p1.aniversario]
}

fact "Elizabeth celebra su aniversario cuatro meses antes que Rodolfo" {
	some disj p1, p2: Pareja |
		(p1.nombreEsposa = Elizabeth) and
		(p2.nombreEsposo = Rodolfo) and
		aniversarioCuatroMesesAntes[p1.aniversario, p2.aniversario]
}

fact "Los Saravia celebran su aniversario cuatro meses despues que Pedro" {
	some disj p1, p2: Pareja |
		(p1.apellido in Saravia) and
		(p2.nombreEsposo = Pedro) and
		aniversarioCuatroMesesAntes[p2.aniversario, p1.aniversario]
}

fact "Los Saravia celebran su aniversario dos meses antes que Marcia" {
	some disj p1, p2: Pareja |
		(p1.apellido in Saravia) and
		(p2.nombreEsposa = Marcia) and
		aniversarioDosMesesAntes[p1.aniversario, p2.aniversario]
}

fact "Daniel y Carla celebran su aniversario ocho meses antes que los Garcia" {
	some disj p1, p2: Pareja |
		(p1.nombreEsposo in Daniel) and
		(p1.nombreEsposa in Carla) and
		(p2.apellido in Garcia) and
		aniversarioOchoMesesAntes[p1.aniversario, p2.aniversario]
}

fact "Miguel celebra su aniversario en Septiembre" {
	some p: Pareja |
		(p.nombreEsposo in Miguel) and
		(p.aniversario in Septiembre)
}


// determina si m1 precede a m2 por la cantidad de dos meses.
pred aniversarioDosMesesAntes[m1, m2: Mes] {
	(m1 in Febrero and m2 in Abril) or
	(m1 in Agosto and m2 in Septiembre)
}

pred aniversarioCuatroMesesAntes[m1, m2: Mes] {
	(m1 in Abril and m2 in Agosto)
}

pred aniversarioOchoMesesAntes[m1, m2: Mes] {
	(m1 in Febrero and m2 in Octubre)
}
