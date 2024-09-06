/*
Considerar el diagrama correspondiente a la definición de un mapeo que relaciona objetos de diferente
tipo: vincula a cada Llave con cero o más Valor, y ambos son Objeto.
*/

sig Objeto {}

sig Llave extends Objeto {
	mapeo: set Valor
}

sig Valor {}

//no deben existir objetos fuera del contexto de mapeos.
fact {all o: Objeto | (o in Llave + Valor)}

//mapeo es una funcion parcial: hay atomos de Llave que no estan mapeados, y los que sí lo están, lo están a un solo Valor
//parcial significa que no todos los atomos del dominio deben estar en la relacion
//funcional significa que tiene el comportamiento de una funcion: un mismo atomo del dominio no puede estar en relacion con multiples atomos de la imagen
assert mapeoFuncionalParcial {
	all k: Llave | (lone k.mapeo)
}

fact mapeoFuncional {
	all k: Llave | (#k.mapeo <= 1)
}

run {}

run llaveNoMapeo {
	some k: Llave | (no k.mapeo)
}

run valorNoMapeo {
	some v: Valor | (no mapeo.v)
}

check mapeoFuncionalParcial

run mismaLlaveDosValores {
	some k: Llave | (#k.mapeo = 2)
}
