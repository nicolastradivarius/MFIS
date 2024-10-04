/*
Considere el siguiente diagrama correspondiente a la definición de un mapeo que relaciona objetos
de diferente tipo...

(a) Escribir modelo en Alloy. No signaturas abstractas ni objetos fuera del contexto de mapeos.

*/

sig Objeto {}

sig Llave extends Objeto {
	mapeo: set Valor
}

sig Valor extends Objeto {}

fact "no existen objetos fuera del contexto de mapeos" {
	all o: Objeto | (o in Llave + Valor)
}

/*
(b) ¿Puede existir un objeto que no sea llave o valor? ¿Por qué? Justifique especificando el
comando correspondiente en Alloy e indique la respuesta brindada por el analizador.
*/

// Alloy no encuentra instancias para este comando, por lo que es posible que no exista.
run objetoNoLlaveNiValor {
	some o: Objeto | (o not in Llave) and (o not in Valor)
} for 5

/*
(c) Utilice una aserción para verificar si el mapeo define una relación funcional parcial entre llaves
y valores. ¿Se verifica la aserción? En caso negativo, añada las restricciones necesarias sobre
el modelo para asegurar que se cumpla esta propiedad
*/

// relación funcional: cada átomo del dominio es mapeado a un único elemento del rango.
// relación parcial: no todos los átomos del dominio son mapeados.
// no se verifica la aserción. Agregamos las restricciones debajo.
assert mapeoRelacionFuncionalParcial {
	all k: Llave | lone k.mapeo
//	all k: Llave | no disj v1, v2: Valor | (v1+v2 in k.mapeo)
}

check mapeoRelacionFuncionalParcial for 4

fact "mapeo es una relación funcional parcial" {
	all k: Llave | lone k.mapeo
//	all k: Llave | one v: Valor | v in k.mapeo
}

/*
(d)  ¿Puede existir una llave que no pertenezca a un determinado mapeo? ¿y un valor?. Intente
generar instancias en las que ocurran estas situaciones. ¿Fue posible generarlas? ¿Por qué?
*/

// sí es posible generar estas instancias ya que mapeo es una relación funcional PARCIAL.
run llaveNoMapeada {
	some k: Llave | no k.mapeo
}

run valorNoMapeado {
	some v: Valor | no mapeo.v
}

/*
(e) Genere una instancia en la que una misma llave se encuentre asociada a dos valores distintos.
¿Qué condición se verifica en tal caso?
*/

// no es posible por lo que discutimos en el inciso (c). La condición que se verifica es la de ser funcional
run mismaLlaveDosValores {
	some k: Llave | #(k.mapeo) > 1
} for 6

run default {} for 6



