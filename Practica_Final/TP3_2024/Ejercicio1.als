sig Colegio {
	id: one ID,
	miembros: some Persona,
	titulares: some Persona,
	suplentes: set Persona,
}

// no es abstracta porque deben existir personas sin profesión.
sig Persona {
	dni: one DNI,
	matricula: lone Matricula
}

abstract sig Matricula {}

sig ID {}

sig DNI {}

sig MatriculaC, MatriculaA, MatriculaF extends Matricula {}

// con extends me aseguro que las profesiones son disjuntas, i.e,
// no hay personas que tengan más de una profesión.
sig Contador, Abogado, Farmaceutico extends Persona {}

sig Provincial, Nacional extends Colegio {}

// este fact me bloquea la dinámica.
--fact "no hay dos colegios con el mismo ID" {
--	no disj c1, c2: Colegio | c1.id = c2.id
--}

fact "no hay dos personas con el mismo dni" {
	no disj p1, p2: Persona | p1.dni = p2.dni
}

fact "no hay dos personas con la misma matrícula" {
//	no disj p1, p2: Persona | p1.matricula = p2.matricula
-- qué pasaría si p1 y p2 no tienen matrícula? este fact no se 
-- satisfacería y por lo tanto el modelo no permitiría que existan
-- personas sin matrícula. La solución es asegurarse que tienen
-- matrícula, y de tenerla, que no sean la misma
	all disj p1, p2: Persona | 
		(some p1.matricula and some p2.matricula) implies
			p1.matricula != p2.matricula
}

fact "la matrícula A corresponde a la profesión de abogado" {
	all p: Persona | 
		p.matricula in MatriculaA implies
			p in Abogado
}

fact "ídem con Farmaceutico" {
	all p: Persona | 
		p.matricula in MatriculaF implies
			p in Farmaceutico
}

fact "ídem con Contador" {
	all p: Persona | 
		p.matricula in MatriculaC implies
			p in Contador
}

fact "cada colegio es de tipo provincial o nacional" {
	Colegio = Provincial + Nacional
}

fact "los titulares y suplentes de un colegio son miembros de éste" {
	all c: Colegio | c.titulares + c.suplentes in c.miembros
}

fact "ningun consejero del colegio puede ser titular y suplente" {
	no titulares & suplentes
}

fact "todos los miembros de un colegio poseen la misma profesion" {
	all c: Colegio, p1, p2: Persona | 
		((p1 in c.miembros) and (p2 in c.miembros)) implies
			mismaProfesion[p1, p2]
}

fact "todos los miembros de un colegio estan matriculados" {
	all c: Colegio, p1, p2: Persona | 
		((p1 in c.miembros) and (p2 in c.miembros)) implies
			matriculados[p1, p2]
}


fact consejoDirectivoColegioProvincial {
	all c: Provincial | 
--		#(c.titulares) >= 1 and // no es necesario por el "some"
		#(c.titulares) <= 3 and
		#(c.suplentes) <= #(c.titulares)
}

fact consejoDirectivoColegioNacional {
	all c: Nacional |
--		#(c.titulares) >= 1 and 
		#(c.titulares) <= 4 and
		#(c.suplentes) <= 2
}

// este fact me bloquea la dinámica, porque no permite que
// haya dos átomos que representen un mismo colegio y por ende
// deban tener los mismos miembros.
--fact "los colegios no comparten miembros" {
--	all disj c1, c2: Colegio | no c1.miembros & c2.miembros
--}

// determina si p1 y p2 tienen la misma profesion.
// por el modelo, una persona tiene a lo sumo una profesion (no más)
pred mismaProfesion[p1, p2: Persona] {
	(p1+p2) in Contador or
	(p1+p2) in Abogado or
	(p1+p2) in Farmaceutico
}

// determina si p1 y p2 están matriculados para la misma profesión.
// esto significa que p1 y p2 deben tener la misma matrícula,
// por ejemplo, la matrícula A.
// El control de que p1 y p2 tengan la matrícula correspondiente
// a su profesión se realiza en un fact.
pred matriculados[p1, p2: Persona] {
	((p1.matricula in MatriculaA) and (p2.matricula in MatriculaA)) or
	((p1.matricula in MatriculaC) and (p2.matricula in MatriculaC)) or
	((p1.matricula in MatriculaF) and (p2.matricula in MatriculaF))
}

run default {}


---------------------- (b) ----------------------

// Añadir una persona al conjunto de miembros de un colegio provincial
// de contadores. Esto es posible siempre y cuando la persona
// pertenezca al consejo directivo de un colegio nacional para esa
// profesión.
pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and
	(p in c2.miembros) and 
	(c1.titulares in c2.titulares) and 
	(c1.suplentes in c2.suplentes)
}

run agregarMiembroCasoExito1 {
	some c1, c2: Colegio, p: Persona | agregarMiembro[c1, c2, p]
}

/*
Irregularidades detectadas: 
- los átomos c1 y c2 son el mismo. Al no ser distintos, no hay forma
de diferenciar la situación del colegio antes y despues de la operación.
- la persona p que se agrega no pertenece al consejo directivo.
- el colegio no es de contadores.
*/

run agregarMiembroCasoExito2 {
	some disj c1, c2: Colegio, p: Persona | agregarMiembro[c1, c2, p]
}

/*
Irregularidades detectadas: 
- la persona ya estaba presente en el colegio antes de ser agregada.
*/

-- la persona ya está en el colegio.
-- Encuentra instancias, por lo que el predicado no controla que
-- la persona no esté previamente en el colegio.
run agregarMiembroCasoNoExito1 {
	some disj c1, c2: Colegio, p: Persona |
		p in c1.miembros and
		agregarMiembro[c1, c2, p]
}

-- La persona está en el consejo de otro colegio nacional antes de 
-- agregarla.
-- No encuentra instancias, lo cual es incorrecto ya que
-- se cumple la condición de que la persona pertenezca al consejo
-- de un colegio nacional antes de ser agregada.
run agregarMiembroCasoExito3 {
	some c1, c2: Provincial, c3: Nacional, p: Persona | 
		p in c3.titulares and
		agregarMiembro[c1, c2, p]
} for 9

-- Verifico que siempre que se agregue un miembro a un colegio provincial,
-- éste sea Contador.
-- Encuentra contraejemplos, donde la persona que se agrega es
-- Abogado o Farmaceutico.
check agregarMiembroSiempreContador {
	all c1, c2: Colegio, p: Persona | 
		agregarMiembro[c1, c2, p] implies (p in Contador)
}





---------------------- (c) ----------------------



pred agregarMiembroCorregido[c1, c2: Provincial, p: Contador] {
	-- *Precondiciones*
	-- El colegio es provincial y de contadores.
	(c1+c2 in Provincial) and
	(p in Contador) and
	-- La persona no está entre los miembros del colegio.
	(p not in c1.miembros) and
	-- La persona está en el consejo de un colegio nacional de contadores.
	(some c: Nacional | p in c.(titulares+suplentes) and c.id != c1.id) and
	-- *Postcondiciones*
	-- La persona se agrega al conjunto de miembros.
	(c2.miembros = c1.miembros + p) and
	-- *Condiciones de marco*
	-- El consejo directivo sigue siendo el mismo.
--	(c2.(titulares+suplentes) = c1.(titulares+suplentes)) and -- esto no
	-- sirve porque sólo chequeamos que su unión sea la misma, mas no los
	-- conjuntos (o relaciones) individuales, que pueden diferir (mientras
	-- la unión dé igual, no pasa nada).
	(c2.titulares = c1.titulares) and
	(c2.suplentes = c1.suplentes) and
	-- El ID sigue siendo el mismo.
	(c2.id = c1.id)
}

-- Siempre que se agrega un miembro al colegio, éste es Contador.
check agregarMiembroCorregidoSiempreContador {
	all c1, c2: Colegio, p: Persona | 
		agregarMiembroCorregido[c1, c2, p] implies (p in Contador)
} for 10

run agregarMiembroCorregidoCasoExito1 {
	some c1, c2: Colegio, p: Persona | agregarMiembroCorregido[c1, c2, p]	
}

-- Siempre que se agregue un miembro, aumentará el número de miembros 
-- en el colegio.
check agregarMiembroCorregidoAumentaNumeroMiembros {
	all c1, c2: Colegio, p: Persona |
		(#(c1.miembros) = 1 and agregarMiembroCorregido[c1, c2, p]) 
			implies 
				(#(c2.miembros) = 2)
} for 10


-- No existen colegios nacionales a los que pudiera pertenecer p.
run agregarMiembroCorregidoCasoNoExito1 {
	some c1, c2: Colegio, p: Persona | 
		no Nacional and
		agregarMiembroCorregido[c1, c2, p]
} for 9


-- Sólo hay una persona. No encuentra instancias debido a que si sólo
-- hay una persona, como todo colegio debe tener al menos un miembro (y
-- al menos un titular), entonces "c1" debería no tener miembros para
-- que c2 tenga al que se quiere agregar, pero esto es incorrecto.
run agregarMiembroCorregidoCasoNoExito2 {
	some c1, c2: Colegio, p: Persona |
		#Persona = 1 and
		agregarMiembroCorregido[c1, c2, p]
} for 10

-- Hay miembros del colegio que son Abogados. Como la profesión de los miembros
-- del colegio determina la categoría del mismo, es imposible agregar un
-- Contador a un colegio de Abogados. Por ende, no hay instancias.
run agregarMiembroCorregidoCasoNoExito3 {
	some c1, c2: Colegio, p: Persona |
		some (c1.miembros & Abogado) and
		agregarMiembroCorregido[c1, c2, p]
} for 10


---------------------- (d) ----------------------

-- Función que permite obtener el conjunto de abogados o farmaceuticos que
-- son consejeros titulares del consejo directivo de al menos un colegio,
-- y son consejeros suplentes de a lo sumo un colegio.
fun AbogadosOFarmaceuticosConsejeros: set Persona {

	{p: Abogado+Farmaceutico | 
		(some c1: Colegio | p in c1.titulares) and
		(lone c2: Colegio | p in c2.suplentes)
	}


	-- ¿si se buscara que sean titulares de un colegio, y suplentes de a lo
	-- sumo OTRO colegio, entonces se haría así? No, porque esto tiene el problema
	-- de que si el "lone" decide ser cero, entonces automaticamente es válida la
	-- condición que se busca cumplir para p, entonces p no sería titular o 
	-- suplente de algún colegio y calificaría para pertenecer al conjunto igual.
/*
	{p: Abogado+Farmaceutico |
		(some c1: Colegio | 
			lone c2: Colegio | 
				c1 != c2 and
				p in c1.titulares and
				p in c2.suplentes
		)
	}
*/
}

run AbogadosOFarmaceuticosConsejerosCasoExito1 {
	some AbogadosOFarmaceuticosConsejeros
} for 6

-- Hay abogados o farmaceuticos que son suplentes de algún colegio (max 1)
run AbogadosOFarmaceuticosConsejerosCasoExito2 {
	some AbogadosOFarmaceuticosConsejeros and 
	some c: Colegio | some AbogadosOFarmaceuticosConsejeros & c.suplentes
} for 6

run AbogadosOFarmaceuticosConsejerosCasoExito2 {
	some AbogadosOFarmaceuticosConsejeros and 
	some c: Colegio | #(AbogadosOFarmaceuticosConsejeros & c.titulares) > 1
} for 6


-- Se busca una instancia que respete que:
-- 			- haya átomos en el conjunto,
-- 			- haya algún colegio donde esos abogados o farmaceuticos son
-- 			miembros, pero no pertenecen al consejo directivo,
-- 			- no haya colegios donde esos bogas y fmcs sean parte del CD.
run AbogadosOFarmaceuticosConsejerosCasoNoExito1 {
	some AbogadosOFarmaceuticosConsejeros and 
	(some c: Colegio | 
		some AbogadosOFarmaceuticosConsejeros & c.miembros and
		no AbogadosOFarmaceuticosConsejeros & c.(titulares+suplentes)
	) and
	no c2: Colegio | some AbogadosOFarmaceuticosConsejeros & c2.(titulares+suplentes)
} for 17
