sig Vehiculo {
	patente: lone Patente,
	titulares: set Persona,
	autorizados: set Persona
}

sig Persona {
	licencia: lone LicenciaConducir,
	dni: one DNI
}

sig Patente {}

sig LicenciaConducir {}

sig DNI {}

sig Gerencial, Comercial, Proveeduria extends Vehiculo {}

sig Menor, Mayoria16, Mayoria18 in Persona {}

fact "los mayores de 18 años son también mayores de 16 años" {
	Mayoria18 in Mayoria16
}

fact "los menores no son mayores de 16 ni de 18" {
	no Menor & Mayoria16 and
	no Menor & Mayoria18
}

fact "no hay dos personas distintas con el mismo dni" {
	no disj p1, p2: Persona | p1.dni = p2.dni
}

fact "las personas son los menores, mayores de 16 y de 18" {
	Persona = Menor + Mayoria16 + Mayoria18
-- Persona - Menor - Mayoria16 = none
}

fact "no hay dos vehiculos distintos con la misma patente" {
	-- Las instancias donde haya dos vehiculos con patente,
	-- y que sea la misma, no formarán parte del modelo.
	-- Pero las instancias donde uno de los dos autos, o ambos,
	-- no tengan patente, tampoco formarán parte del modelo, porque
	-- se haría antecedente falso -> implicación verdadera.
	-- La forma en que se interpreta este fact es que no debe 
	-- haber dos pares de vehículos tal que lo de después de la
	-- barra "|" se haga verdadero. Si v1 o v2 no tienen patente,
	-- la implicación se hace verdadera y no debería ser válida, 
	-- cuando sí lo es.
/*
-- Sin corregir
	no disj v1, v2: Vehiculo | 
		(some v1.patente and some v2.patente) implies
			(v1.patente = v2.patente)

Si se quisiera usar la misma estructura, entonces en vez de
un implies, tendría que haber un AND. En ese caso, se buscaría
que las instancias donde se cumplen las tres condiciones al mismo
tiempo no formen parte del modelo.
Si uno de los dos autos no tuviera patente, por la cadena de ANDs
la sentencia se haría falsa y no hay problema con eso porque lo 
que se busca (como se dijo antes) es que lo de después de la barra
no se haga verdadero.
*/


-- Corregido
	all disj v1, v2: Vehiculo |
		(some v1.patente and some v2.patente) implies
			(v1.patente != v2.patente)
}

-- Buscamos dos autos tales que uno tenga patente y el otro no.
-- No encuentra instancias con la definición del fact anterior
-- sin corregir.
run test1 {
	some disj v1, v2: Vehiculo | some v1.patente and no v2.patente
} for 19

-- Chequeamos que en todas aquellas instancias donde hay más
-- de un auto presente en el conjunto Vehículo, los mismos tienen
-- patente y no se da la posibilidad de que no la tengan.
-- Aquellas instancias donde haya un solo auto, pasarán de largo
-- porque v1 = v2 entonces el check es verdadero.
-- Esto es para probar que el fact está mal diseñado porque 
-- evita que pueda haber autos sin patente cuando son más de 1.
check test2 {
	all v1, v2: Vehiculo | 
		(v1 != v2) implies (some v1.patente and some v2.patente)
} for 19

fact "no hay personas distintas con la misma licencia" {
	no disj p1, p2: Persona |
		some p1.licencia and
		some p2.licencia and
		p1.licencia = p2.licencia
}

fact "cada vehiculo es de un tipo" {
	Vehiculo = Gerencial + Comercial + Proveeduria
}

fact "las personas se encuentran clasificadas por su edad" {
	Persona = Menor + Mayoria16 + Mayoria18
}

fact "no hay un titular y autorizado al mismo tiempo" {
	no titulares & autorizados
}

fact "los vehiculos con patente poseen entre uno y dos titulares" {
	all v: Vehiculo | 
		(some v.patente) implies 
			(#(v.titulares) >= 1 and #(v.titulares) <= 2)
}

fact "los vehiculos no patentados no poseen titulares ni autoriz" {
	all v: Vehiculo | 
		(no v.patente) implies (no v.(titulares+autorizados))
}

fact "los titulares deben poseer al menos 18 años" {
	all v: Vehiculo | v.titulares in Mayoria18
}

fact "los autorizados requieren tener mas de 16 años" {
	all v: Vehiculo | v.autorizados in Mayoria16
}

fact "solo pueden tener licencia los mayores de 16 años" {
	all p: Persona | 
		(some p.licencia) implies p in Mayoria16
}

fact "los vehiculos gerenciales no pueden tener más de un titular" {
	all v: Gerencial | lone v.titulares
}

fact "los vehiculos de proveeduria poseen maximo 3 autorizados" {
	all v: Proveeduria | #(v.autorizados) <= 3
}
