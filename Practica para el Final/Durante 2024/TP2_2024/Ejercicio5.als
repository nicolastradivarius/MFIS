sig Objeto {}

sig Llave extends Objeto {
	mapeo: set Valor
}

sig Valor extends Objeto {}

fact "no existen objetos fuera del contexto de mapeos" {
	(no l: Llave | no l.mapeo) and
	(no v: Valor | no mapeo.v)
}

run default {}

fact "no existe un objeto que no sea llave ni valor" {
	Objeto = Llave + Valor
}

run objetoQueNoEsLlaveNiValor {
	some o: Objeto | o !in Llave and o !in Valor
}

assert mapeoRelacionFuncionalParcial {
	// funcional significa que no hay un mismo átomo del
	// dominio mapeado a múltiples átomos del rango.
	// parcial significa que no todo el dominio es mapeado.
	all key: Llave | #(key.mapeo) <= 1
		
}

// no se verifica.
check mapeoRelacionFuncionalParcial for 6

// añadimos la restricción para que la aserción se verifique.
fact "no hay una misma llave mapeada a múltiples valores" {
	all key: Llave | lone key.mapeo
}

// no es posible generar instancias. Esto se debe al hecho de
// que no existen objetos fuera del contexto de mapeos. A mi
// entendimiento significa que no existen átomos de Objeto que
// no estén presentes en algún mapeo. Esto implica que "mapeo"
// es una relación total.
run llaveNoPerteneceAMapeo {
	some key: Llave | no key.mapeo
} for 7

