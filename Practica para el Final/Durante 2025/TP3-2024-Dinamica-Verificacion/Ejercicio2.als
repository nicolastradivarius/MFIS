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

fact {no Vehiculo - Proveeduria - Comercial - Gerencial}

fact {all v: Vehiculo | (some v.placa) implies (some v.titulares and #v.titulares < 3)}

fact {no v: Vehiculo | some (v.titulares & v.autorizados)}

fact {no v: Vehiculo | (no v.placa) and ((some v.titulares) or (some v.autorizados))}

fact {no disj p1, p2: Persona | (p1.id = p2.id)}

fact {no Persona - Menor - Mayoria16 - Mayoria18}

fact {no Menor & Mayoria16}

fact {no Menor & Mayoria18}

fact {Mayoria18 in Mayoria16}

// si la persona es titular de algun vehiculo, tiene que tener 18 anios o mas.
fact {all p: Persona| (some titulares.p) implies (p in Mayoria18)}

fact {all p: Persona | (some autorizados.p) implies (p in Mayoria16)}

fact {all p: Persona | (some p.carnet) implies (p in Mayoria16)}

fact {all vg: Gerencial | lone vg.titulares}

fact {all vp: Proveeduria | #(vp.autorizados) < 4}

fact {no disj p1, p2: Persona | 
	(some p1.carnet) and (some p2.carnet) and (p1.carnet = p2.carnet)
}

// No hay dos vehiculos distintos con la misma placa. Bloquea la dinamica
//fact {no disj v1, v2: Vehiculo | (some v1.placa) and (some v2.placa) and (v1.placa = v2.placa)}

------------------

// agrega una persona al conjunto de autorizados para manejar un vehiculo de proveeduria.
// esto es posible siempre que la persona posea la licencia y la cantidad original de 
// autorizados no supere a la cantidad de titulares.
pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)
}

run agregarAutorizado

/*
Problemas detectados con agregarAutorizado:
- hay instancias donde v1 y v2 son el mismo átomo. Esto impide ver la evolucion en el tiempo.
- el vehiculo en cuestion no es de Proveeduria.
- en las instancias donde v1 y v2 son distintos atomos, son de distinto tipo (no respeta inv)
*/

check agregarAutorizadoTeniaAutorizadosMenosQueTitulares {
	all disj v1, v2: Vehiculo, p: Persona | 
		agregarAutorizado[v1, v2, p] implies #(v1.autorizados) <= #(v1.titulares)
}
-- Encuentra contraejemplos donde el vehiculo tenia mas autorizados que titulares.

check agregarAutorizadoTieneLicencia {
	all disj v1, v2: Vehiculo, p: Persona | 
		agregarAutorizado[v1, v2, p] implies some p.carnet
} for 10
-- No encuentra contraejemplos por lo que esta parte esta bien modelada.

------------- (d) -------------------

// agrega una persona al conjunto de autorizados para manejar un vehiculo de proveeduria.
// esto es posible siempre que la persona posea la licencia y la cantidad original de 
// autorizados no supere a la cantidad de titulares.
pred agregarAutorizadoV2[v1, v2: Vehiculo, p: Persona] {
	// Precondiciones
	-- El vehiculo es de proveeduria
	(v1 in Proveeduria) and
	-- La persona no era autorizada del vehiculo previamente
	(p not in v1.autorizados) and
	-- La persona posee licencia de conducir
	(some p.carnet) and
	-- La cantidad original de autorizados no supera a la de titulares
	(#(v1.autorizados) <= #(v1.titulares)) and
	
	// Postcondiciones
	-- La persona ahora esta autorizada a conducir el vehiculo
	(v2.autorizados = v1.autorizados + p) and
	
	// Invariantes
	-- Los titulares del vehiculo son los mismos
	(v2.titulares = v1.titulares) and
	-- La placa del vehiculo es la misma
	(v2.placa = v1.placa) and
	-- El vehiculo es el mismo
	(v2 in Proveeduria)
}

run agregarAutorizadoV2 

------ (d) ----------

/*
Definir funcion que permita obtener el conjunto de personas que poseen al menos 18 anios,
no tienen carnet de conducir y son titulares de algun vehiculo comercial o gerencial.
*/

fun titularesSinCarnet[]: set Mayoria18 {
	{p: Mayoria18 | 
		(no p.carnet) and 
		(some v: Comercial+Gerencial | p in v.titulares)
	}
}

run algunosTitularesSinCarnet {
	some titularesSinCarnet
}

--------- (e) -----------

// modela el traspaso de un autorizado a ser titular del vehiculo.
// para que sea posible el traspaso, la persona no debe ser titular de un vehiculo de distinto
// tipo al vehiculo para el cual se esta realizando el traspaso.
// Luego del traspaso, el vehiculo debera contar con al menos una persona autorizada para
// manejarlo.
pred autorizadoATitular[v1, v2: Vehiculo, p: Persona] {
	// Precondiciones
	-- La persona esta previamente autorizada a conducir el vehiculo
	(p in v1.autorizados) and
	-- La persona no es titular del vehiculo
	(p not in v1.titulares) and
	-- La persona no es titular de otro tipo de vehiculo (puede ser titular de otro del mismo tipo)
	(all v3: Vehiculo - {v1} - {v2} | 
		(p in v3.titulares implies (
			v1+v3 in Proveeduria or 
			v1+v3 in Comercial or 
			v1+v3 in Gerencial
			)
		)
	) and
	
	// Postcondiciones
	-- La persona ahora es titular del vehiculo y ya no es mas autorizada
	(v2.titulares = v1.titulares + p) and
	(v2.autorizados = v1.autorizados - p) and
	(p not in v2.autorizados) and
	-- El vehiculo cuenta con al menos un autorizado
	(some v2.autorizados) and

	// Invariantes
	-- La placa del vehiculo es la misma
	(v2.placa = v1.placa) and
	-- El resto de los vehiculos no tienen dicha placa
	(all v3: Vehiculo - {v1} - {v2} | v3.placa != v1.placa) and
	-- El vehiculo es el mismo
	(
		(v1+v2 in Proveeduria) or 
		(v1+v2 in Comercial) or 
		(v1+v2 in Gerencial)
	)
}

run autorizadoATitular

// caso donde la persona es titular de otro auto del mismo tipo al de en cuestion
run autorizadoATitularCasoExito1 {
	some disj v1, v2, v3: Vehiculo, p: Persona |
		(v1+v3 in Proveeduria) and
		(p in v3.titulares) and
		autorizadoATitular[v1, v2, p]
}

// caso donde controlamos la cardinalidad de las relaciones en funcion del exito del predicado
check autorizadoATitularCasoExito2 {
	all disj v1, v2: Vehiculo, p: Persona |
		(#(v1.titulares) = 1 and autorizadoATitular[v1, v2, p]) implies
			(#(v2.titulares) = 2)
} for 10

// Caso donde solo hay una placa.
run autorizadoATitularCasoExito3 {
	some disj v1, v2: Vehiculo, p: Persona |
		one Patente and
		autorizadoATitular[v1, v2, p]
}

// Caso donde el vehiculo es gerencial y ya tiene un tutorial (maximo 1 titular).
run autorizadoATitularCasoNoExito1 {
	some disj v1, v2: Vehiculo, p: Persona |
		v1 in Gerencial and
		some v1.titulares and
		autorizadoATitular[v1, v2, p]
} for 10
// No encuentra instancias porque no se puede agregar un titular mas, habrian dos.

// caso donde la persona es titular de otro auto de un tipo diferente al de en cuestion
run autorizadoATitularCasoNoExito2 {
	some disj v1, v2, v3: Vehiculo, p: Persona |
		(v1 in Proveeduria) and
		(v3 in Gerencial) and
		(p in v3.titulares) and
		autorizadoATitular[v1, v2, p]
} for 6
// No encuentra instancias porque no puede darse esta situacion.

// Caso donde la persona que se quiere hacer titular tiene menos de 18 anios.
run autorizadoATitularCasoNoExito3 {
	some disj v1, v2: Vehiculo, p: Persona |
		(p not in Mayoria18) and
		autorizadoATitular[v1, v2, p]
} for 10
// No encuentra instancias dado que todos los titulares de un vehiculo deben tener mas de 18.





