sig Vehiculo {
	titulares: set Persona, 
	autorizados: set Persona, 
	placa: lone Patente
}

sig Proveeduria, Comercial, Gerencial extends Vehiculo {}

sig Patente {}

sig Persona {
	id: one DNI,
	carnet: lone LicenciaConducir
}

sig Mayoria18, Mayoria16, Menor in Persona {}

sig DNI {}

sig LicenciaConducir {}

fact "cada vehiculo es de tipo Gerencial, Comercial o Proveeduria" {
	no Vehiculo - Proveeduria - Comercial - Gerencial
}

fact "los vehiculos con patente poseen entre uno y dos titulares" {
	all v: Vehiculo | (some v.placa) implies (some v.titulares and #v.titulares < 3)
}

fact "los titulares y autorizados de un vehiculo son personas diferentes" {
	no v: Vehiculo | some (v.titulares & v.autorizados)
}

fact {no v: Vehiculo | (no v.placa) and ((some v.titulares) or (some v.autorizados))}

fact {no disj p1, p2: Persona | (p1.id = p2.id)}

fact {no Persona - Menor - Mayoria16 - Mayoria18}

fact {no Menor & Mayoria16}

fact {no Menor & Mayoria18}

fact {Mayoria18 in Mayoria16}

fact {all p: Persona| (some titulares.p) implies (p in Mayoria18)}

fact {all p: Persona | (some autorizados.p) implies (p in Mayoria16)}

fact {all p: Persona | (some p.carnet) implies (p in Mayoria16)}

fact {all vg: Gerencial | lone vg.titulares}

fact {all vp: Proveeduria | #(vp.autorizados) < 4}

fact {no disj p1, p2: Persona | (some p1.carnet) and (some p2.carnet) and (p1.carnet = p2.carnet)}

// me bloquea la dinámica
//fact {no disj v1, v2: Vehiculo | (some v1.placa) and (some v2.placa) and (v1.placa = v2.placa)}


-------------------- Dinámica -------------------------


/**
Este predicado modela el comportamiento de añadir una 
persona al conjunto de personas autorizadas a manejar un vehiculo de proveeduria. Esta accion 
es posible siempre y cuando la persona posea licencia de conducir y la cantidad original de 
personas autorizadas a manejar el vehiculo no supere a la cantidad de titulares del mismo.
*/
pred agregarAutorizadoV1[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and 
	(p in v2.autorizados) and 
	(v2.titulares = v1.titulares)
}

run agregarAutorizadoV1_CasoExito1 {
	some v1, v2: Vehiculo, p: Persona | agregarAutorizadoV1[v1, v2, p]
}

/*
En la primer instancia, se detectan irregularidades:
- los vehiculos v1 y v2 son el mismo átomo, de esa manera nunca se puede lograr que
la persona que se quiere añadir al conjunto de autorizados no esté previamente en él.
- suponiendo que la persona ya era autorizado para conducir, entonces la operación
está teniendo éxito aún cuando no se efectuó.
- siguiendo con la suposición, había más personas autorizadas que titulares del vehículo.
*/

run agregarAutorizadoV1_CasoExito2 {
	some disj v1, v2: Vehiculo, p: Persona | agregarAutorizadoV1[v1, v2, p]
}

/*
En la primer instancia, se detectan irregularidades:
- v1 tiene más autorizados que titulares.
- v1 y v2 son distintos tipos de vehiculo, no están representando al mismo vehiculo, 
además difieren en su placa. Deberían ser de tipo Proveeduría.
*/

// despues de agregar un autorizado, la cantidad de autorizados de v2 es mayor que v1
check agregarAutorizadoV1_CasoExito3 {
	all disj v1, v2: Vehiculo, p: Persona | agregarAutorizadoV1[v1, v2, p] implies #(v2.autorizados) > #(v1.autorizados)
}

/*
Falla, la primer instancia muestra que v2 tiene sólo el autorizado que "se agregó", mientras v1 tiene a ese y a otro.
*/

/**
Rehacemos el predicado.
*/
pred agregarAutorizadoV2[v1, v2: Vehiculo, p: Persona] {
	// Precondiciones
	-- la persona no estaba autorizada a conducir el vehiculo
	(p not in v1.autorizados) and
	-- la persona posee carnet
	(some p.carnet) and
	-- la cantidad original de personas autorizadas a manejar el vehiculo no supera a la cantidad de titulares del mismo
	(#(v1.autorizados) <= #(v1.titulares)) and
	-- el vehiculo es de proveeduria
	(v1 in Proveeduria) and
	// Postcondiciones
	-- la persona se agrega al conjunto de autorizados
	(v2.autorizados = v1.autorizados + p) and
	// Condición de marco
	-- los titulares y la placa del vehiculo siguen siendo las mismas
	(v2.titulares = v1.titulares) and
	(v2.placa = v1.placa)
}

run agregarAutorizadoV2_CasoExito1 {
	some disj v1, v2: Vehiculo, p: Persona | agregarAutorizadoV2[v1, v2, p]
} for 16

// cada vez que se agregue un autorizado, la cantidad de autorizados de v2 va a superar la de v1
check agregarAutorizadoV2_CasoExito2 {
	all disj v1, v2: Vehiculo, p: Persona | agregarAutorizadoV2[v1, v2, p] implies #(v2.autorizados) > #(v1.autorizados)
} for 16


// la cantidad de titulares del vehiculo es 2. por consiguiente, los autorizados deben ser 2 o menos
run agregarAutorizadoV2_CasoExito3 {
	some disj v1, v2: Vehiculo, p: Persona | 
		#(v1.titulares) = 2 and agregarAutorizadoV2[v1, v2, p]
} for 10

// el vehiculo ya tiene 3 autorizados, con lo cual no deberia poder agregarsele otro.
// efectivamente falla en encontrar instancias porque viola la restricción de que
// un vehiculo de proveeduría posee un máximo de 3 autorizados.
run agregarAutorizadoV2_CasoNoExito1 {
	some disj v1, v2: Vehiculo, p: Persona | #(v1.autorizados) = 3 and agregarAutorizadoV2[v1, v2, p]
} for 20

// la persona que se quiere autorizar es menor de 16 años.
// efectivamente falla porque viola la restricción de que los autorizados deben tener al menos 16
run agregarAutorizadoV2_CasoNoExito2 {
	some disj v1, v2: Vehiculo, p: Persona | p in Menor and agregarAutorizadoV2[v1, v2, p]
} for 20

// el vehiculo no tiene patente.
// claramente no va a encontrar instancias porque un vehiculo sin patente no puede tener
// autorizados (ni titulares)
run agregarAutorizadoV2_CasoNoExito3 {
	some disj v1, v2: Vehiculo, p: Persona | (no v1.placa) and agregarAutorizadoV2[v1, v2, p]
} for 30
