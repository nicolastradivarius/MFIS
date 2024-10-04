/*
Toda persona se encuentra identificada por su DNI y tiene a lo sumo una profesion. Por otra parte, 
una persona puede o no encontrarse matriculada para la profesion que tenga. Cada colegio es de un 
tipo: provincial o nacional. Los colegios poseen un numero que los identifica, y su consejo directivo 
se encuentra conformado por un conjunto de consejeros titulares y otro conjunto de consejeros 
suplentes, todos los cuales son ademas miembros del colegio. Ningun consejero de un Colegio 
puede ser titular y suplente a la vez. Todos los miembros de un colegio poseen la misma profesion y 
se encuentran matriculados para dicha profesion, siendo esa profesion la que determina la categorıa 
del colegio. El consejo directivo de un colegio provincial posee entre 1 y 3 consejeros titulares, y la 
cantidad de consejeros suplentes no puede superar a la cantidad de titulares. Por ultimo, el consejo 
directivo de un colegio nacional posee entre 1 y 4 consejeros titulares, y un maximo de 2 suplentes.
*/

------------------- Modelo validado por la Cátedra -------------------

sig Colegio {
	miembros: some Persona, 
	titulares: some Persona,
	suplentes: set Persona, 
	id: one ID
}

sig Provincial, Nacional extends Colegio {}

sig ID {}

sig Persona {
	dni: one DNI,
	matricula: lone Matricula
}

sig Contador, Abogado, Farmaceutico extends Persona {}

sig DNI {}

abstract sig Matricula {}

sig MatriculaC, MatriculaA, MatriculaF extends Matricula {}


------------------- Restricciones del modelo -------------------

fact "todas las personas tienen DNI distinto" {
	all disj p1, p2: Persona | p1.dni != p2.dni
}

fact "las personas matriculadas tienen matrícula distinta" {
	no disj p1, p2: Persona | 
		(some p1.matricula) and (some p2.matricula) and (p1.matricula = p2.matricula)
}

/*
// me bloquea la dinámica
fact "los colegios tienen ID distinto" {
	all disj c1, c2: Colegio | c1.id != c2.id
}
*/

fact "los colegios pueden ser provinciales o nacionales" {
	Colegio = (Provincial+Nacional)
}

fact "ningun consejero de un colegio puede ser titular y suplente a la vez" {
	all c: Colegio | no (c.titulares & c.suplentes)
}

fact "todos los consejeros del colegio son miembros del mismo" {
	all c: Colegio | (c.titulares + c.suplentes) in c.miembros
}

fact "si la matricula de una persona es la C entonces su profesión es Contador" {
	all p: Persona | (some (MatriculaC & p.matricula)) implies (p in Contador)
}

fact "si la matricula de una persona es la A entonces su profesión es Abogado" {
	all p: Persona | (some (MatriculaA & p.matricula)) implies (p in Abogado)
}

fact "si la matricula de una persona es la F entonces su profesión es Farmacéutico" {
	all p: Persona | (some (MatriculaF & p.matricula)) implies (p in Farmaceutico)
}

fact "todos los miembros de un colegio poseen la misma profesion y estan matriculados para tal" {
	all p1, p2: Persona, c: Colegio |
		((p1 in c.miembros) and (p2 in c.miembros)) implies 
			(mismaProfesion[p1,p2] and matriculadosParaMismaProfesion[p1,p2])
}

fact "el consejo directivo de colegio provincial tiene hasta 3 titulares y los suplentes no lo superan" {
	all c: Provincial | (#c.titulares =< 3) and (#c.suplentes =< #c.titulares)
}

fact "el consejo directivo de colegio nacional tiene hasta 4 titulares y hasta 2 suplentes" {
	all c: Nacional | (#c.titulares =< 4) and (#c.suplentes =< 2)
}


------------------- Funciones y Predicados -------------------

// determina si dos personas son de la misma profesión
pred mismaProfesion[p1, p2: Persona] {
	(p1+p2 in Contador) or (p1+p2 in Abogado) or (p1+p2 in Farmaceutico)
}

// determina si dos personas estan matriculadas para la misma profesión
pred matriculadosParaMismaProfesion[p1, p2: Persona] {
	((some (p1.matricula & MatriculaC)) and (some (p2.matricula & MatriculaC))) or
	((some (p1.matricula & MatriculaA)) and (some (p2.matricula & MatriculaA))) or 
	((some (p1.matricula & MatriculaF)) and (some (p2.matricula & MatriculaF)))
}

// modela el comportamiento de añadir una persona al conjunto de miembros de un 
// colegio provincial de contadores. Esta accion es posible siempre y cuando la persona 
// pertenezca al consejo directivo de un colegio nacional para esa profesión:
pred agregarMiembro_v1[c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and
	(p in c2.miembros) and 
	(c1.titulares in c2.titulares) and 
	(c1.suplentes in c2.suplentes) and
	(c1.id = c2.id)
}

// Corregimos el comportamiento del predicado anterior.
// Cambiamos los parámetros para asegurar que los colegios donde se quiere
// modelar dinámica sean provinciales, y como son colegios de contadores, la
// persona a agregar debe ser contador.
pred agregarMiembro_v2[c1, c2: Provincial, p: Contador] {
	// Precondiciones:
	// existe un colegio nacional donde la persona es parte del consejo
	(some c3: Nacional | p in c3.(titulares+suplentes)) and
	// la persona no es miembro del colegio al que se lo quiere agregar
	(p not in c1.miembros) and 
	// Postcondiciones:
	// la persona se agregó al colegio
	(c2.miembros = c1.miembros + p) and
	// Condición de marco:
	// el consejo directivo del colegio sigue siendo el mismo
	(c1.titulares = c2.titulares) and
	(c1.suplentes = c2.suplentes) and
	(c1.id = c2.id)
}

pred agregarMiembro_v3[c1, c2: Provincial, p: Contador] {
	// Precondiciones:
	// la persona que se quiere agregar es efectivamente un contador
	(p in Contador) and
	// los colegios son provinciales
	(c1+c2) in Provincial and
	// existe un colegio nacional donde la persona es parte del consejo
	(some c3: Nacional | p in c3.(titulares+suplentes)) and
	// la persona no es miembro del colegio al que se lo quiere agregar
	(p not in c1.miembros) and 
	// Postcondiciones:
	// la persona se agregó al colegio
	(c2.miembros = c1.miembros + p) and
	// Condición de marco:
	// el consejo directivo del colegio sigue siendo el mismo
	(c1.titulares = c2.titulares) and
	(c1.suplentes = c2.suplentes) and
	// el id es el mismo
	(c1.id = c2.id)
}


------------------- Validación del modelo -------------------

run default {}

/*
Tiene exito, y se detectan irregularidades en la primer instancia:
	- la persona que se "agregó" al colegio es farmaceutico, no contador. Esto no
	tendría sentido dado que los colegios son de contadores.
	- el átomo del colegio inicial (c1) ya tenía a la persona como miembro, lo cual
	debería evitar que se agregara.
	- el colegio final (c2) tiene a otros miembros que no tenía el átomo del colegio
	inicial, y esto no tiene sentido ya que ambos átomos representan al mismo colegio.
A lo largo de otras instancias, suceden cosas similares, cambiando la profesión, la cantidad
de miembros que varían entre la inicial y la final, etc.
En ninguna de ellas, la persona que se pretende agregar está como miembro
en algún colegio nacional
*/
run agregarMiembroCasoExito {
	some disj c1, c2: Colegio, p: Persona | agregarMiembro_v1[c1, c2, p]
}

// agregar un miembro a un colegio en donde ya es miembro.
// una irregularidad encontrada es que el colegio final tiene más miembros que el inicial, como
// si se hubieran agregado.
run agregarMiembroV1CasoNoExito {
	some disj c1, c2: Colegio, p: Persona | (p in c1.miembros) and agregarMiembro_v1[c1, c2, p]	
}

// agregar un miembro a un colegio NACIONAL donde ya es miembro.
// tiene exito, pero no debería tenerlo porque se está queriendo agregar una persona a un
// colegio nacional, cuando la dinámica involucra provinciales.
run agregarMiembroV1CasoNoExito2 {
	some disj c1, c2: Nacional, p: Persona | (p in c1.miembros) and agregarMiembro_v1[c1, c2, p]	
}


// tiene exito, pero la persona que agrega es un farmacéutico, y por ende, el colegio termina
// siendo de farmaceuticos. Por lo tanto se debe corroborar que la persona que se está
// queriendo agregar sea un Contador.
// Otra irregularidad es que se quieren agregar personas a colegios Nacionales, o incluso,
// el colegio inicial y final difieren en su tipo.
run agregarMiembroV2CasoExito {
	some disj c1, c2: Colegio, p: Persona | agregarMiembro_v2[c1, c2, p]
}

// no encuentra instancias como es de suponer, ya que no se pueden satisfacer ambas condiciones.
run agregarMiembroV2CasoNoExito {
	some disj c1, c2: Colegio, p: Persona | (p in c1.miembros) and agregarMiembro_v2[c1, c2, p]
}

// encuentra instancias
run agregarMiembroV3CasoExito {
	some disj c1, c2: Colegio, p: Persona | agregarMiembro_v3[c1, c2, p]
}

// busca instancias para agregar en donde el colegio tenga el consejo lleno.
run agregarMiembroV3CasoExito1{
	some disj c1, c2: Colegio, p: Persona | 
		(#(c1.titulares) = 3) and (#(c1.suplentes) = 3) and agregarMiembro_v3[c1, c2, p]
} for 7


// busca instancias para agregar en donde sólo hay un colegio nacional y su consejo está lleno
run agregarMiembroV3CasoExito2 {
	some disj c1, c2, c3: Colegio, p: Persona | 
		(c3 = Nacional) and #(c3.titulares) = 4 and #(c3.suplentes) = 2 and #Nacional = 1 and
// 		con esta sola linea se transforma en un caso de no éxito, puesto que p debe estar en 
//		algún colegio nacional.
//		(p not in c3.miembros) and 
		agregarMiembro_v3[c1, c2, p]
} for 6

run agregarMiembroV3CasoNoExito {
	some disj c1, c2: Colegio, p: Persona | not agregarMiembro_v3[c1, c2, p]
}

// busca instancias para agregar en donde la persona no tenga matrícula.
// claramente no encuentra instancias porque si la persona no está matriculada, entonces
// no podría pertenecer al consejo de un colegio nacional, y tampoco podría ser agregada
// como miembro al colegio c1.
run agregarMiembroV3CasoNoExito1 {
	some disj c1, c2: Colegio, p: Persona | 
		(no p.matricula) and agregarMiembro_v3[c1, c2, p]
} for 7

// busca instancias para agregar en donde la persona tenga matrícula A.
// claramente no encuentra instancias porque si la persona tiene matrícula A entonces es abogado,
// y el predicado corrobora que la persona sea contador.
run agregarMiembroV3CasoNoExito2 {
	some disj c1, c2: Colegio, p: Persona | 
		(p.matricula = MatriculaA) and agregarMiembro_v3[c1, c2, p]
} for 7

// busca instancias para agregar en donde el colegio no tiene miembros.
// no encuentra instancias porque contradice el modelo, todo colegio debe tener al menos 1 miembro.
run agregarMiembroV3CasoNoExito3 {
	some disj c1, c2: Colegio, p: Persona | 
		(no c1.miembros) and agregarMiembro_v3[c1, c2, p]
} for 16

// busca instancias para agregar en donde no hay colegios nacionales.
// claramente no encuentra instancias porque la persona p debe pertenecer a algún Nacional
run agregarMiembroV3CasoNoExito4 {
	some disj c1, c2: Colegio, p: Persona | no Nacional and agregarMiembro_v3[c1, c2, p]
} for 7

// busca instancias para agregar dos personas.
// no encuentra instancias ya que, al momento de llamar al predicado la segunda vez,
// lo que falla es la condición de que los miembros de c2 sean los de c1 sumado a p2.
// el problema aquí es que los miembros de c2 eran los de c1 sumado a p1; cuando se hace
// la verificación, los miembros de c2 NO son los de c1 con p2, ya que c2 a esta altura tiene a p1
// y c1 no tiene a p1, con lo cual al compararlos queda dando vuelta el p1 de c2 que hace que
// sean distintos conjuntos. 
// {c2, p1} = {c1} + {p1} es verdadero, pero {c2, p1} = {c1} + {p2} es falso pues c1 no tiene a p1.
run agregarMiembroV3CasoNoExito5{
	some disj c1, c2: Colegio, disj p1, p2: Persona | 
		agregarMiembro_v3[c1, c2, p1] and agregarMiembro_v3[c1, c2, p2]
} for 16


---------------------------------------

/*
Defina una funcion que permita obtener el conjunto de abogados o farmaceuticos que son 
consejeros titulares del consejo directivo de al menos un colegio y son consejeros suplentes de 
a lo sumo un colegio.
*/

fun abogados_farmaceuticos_titulares_suplentes: set Persona {
	{
		p: Abogado+Farmaceutico | 
			some c1: Colegio | 
				lone c2: Colegio |
					(p in c1.titulares) and
					(p in c2.suplentes)
	}
}

run abogados_farmaceuticos_caso_exito {
	some abogados_farmaceuticos_titulares_suplentes
} for 6


// la quinta instancia de este comando tiene una irregularidad: hay un Abogado que es
// considerado por Alloy como parte del conjunto buscado, pero no es miembro de algún colegio;
// es más, no tiene matrícula (lo cual podría ser el motivo), ni es titular o suplente de un colegio.
// es probable que se deba a la forma en que se cuantificó: some c1 | lone c2... es factible de 
// encontrar un colegio c1 tal que haya cero colegios c2 donde se cumpla el statement, y por ende,
// todo lo requerido es válido y el abogado P es válido para el conjunto de retorno.
run abogados_farmaceuticos_varios_colegios_caso_exito {
	#Colegio = 3 and some abogados_farmaceuticos_titulares_suplentes
} for 6

// buscamos dicha instancia en particular.
run abogados_farmaceuticos_varios_colegios_caso_no_exito {
	#Colegio = 3 and 
	some p: Abogado | no miembros.p and p in abogados_farmaceuticos_titulares_suplentes
} for 6

// corregimos la función
fun abogados_farmaceuticos_titulares_suplentesV2: set Persona {
	{
		p: Abogado+Farmaceutico | 
			(some c1: Colegio | (p in c1.titulares)) and
			(lone c2: Colegio | (p in c2.suplentes))
	}
}

run abogados_farmaceuticos_varios_colegios_caso_exito2 {
	#Colegio = 3 and some abogados_farmaceuticos_titulares_suplentesV2
} for 6

run abogados_farmaceuticos_varios_colegios_caso_no_exito2 {
	#Colegio = 3 and 
	some p: Abogado | no miembros.p and p in abogados_farmaceuticos_titulares_suplentesV2
} for 6


--------------------------------------


/*
Defina un predicado que modele el comportamiento de realizar el traspaso de un consejero
suplente del consejo directivo de un colegio a su conjunto de consejeros titulares:

Para que dicha accion pueda realizarse la persona no debe formar parte del consejo directivo de 
un colegio con distinto identificador que el colegio para el cual se esta realizando el traspaso. 
Ademas, luego del traspaso, el colegio debera contar con al menos un consejero suplente. 
Debera explicitarse toda pre y post-condicion asociada a la accion, incluyendo las indicadas 
en la descripcion brindada, ası como tambien las condiciones de marco.

Valide el predicado definido, considerando al menos 3 casos de exito y 3 casos de no exito.
*/

pred suplenteATitular[c1, c2: Colegio, p: Persona] {
	// Precondiciones:
	-- la persona es suplente en el colegio
	(p in c1.suplentes) and
	-- la persona no está en el consejo de otro colegio aparte del involucrado
	(no c3: Colegio | (c3.id != c1.id) and (p in c3.(titulares+suplentes))) and
	// Postcondiciones:
	-- los titulares del colegio son los mismos que antes, sumando a la nueva persona
	(c2.titulares = c1.titulares + p) and
	-- los suplentes del colegio son los mismos que antes, quitando a la nueva persona
	(c2.suplentes = c1.suplentes - p) and
	-- el colegio cuenta con al menos un consejero suplente
	(some c2.suplentes) and
	// Condiciones de marco:
	-- los miembros del colegio son los mismos
	(c2.miembros = c1.miembros) and
	-- el id del colegio es el mismo
	(c2.id = c1.id) and
	-- el tipo de colegio es el mismo
	((c1+c2 in Provincial) or (c1+c2 in Nacional))
}


// la primer instancia muestra una irregularidad: c1 es colegio Provincial y c2 es Nacional
// se supone que deben ser el mismo colegio.
// se corrige con la última restricción añadida en el predicado.
run suplenteATitularCasoExito {
	some c1, c2: Colegio, p: Persona | suplenteATitular[c1, c2, p]
}

// la persona está en el conjunto de miembros de otro colegio aparte, pero no es parte del consejo
run suplenteATitularCasoExito2 {
	some disj c1, c2, c3: Colegio, p: Persona | (p in c3.miembros) and suplenteATitular[c1, c2, p]
}

// el colegio es provincial y tiene 1 menos que el máximo de titulares y de suplentes
run suplenteATitularCasoExito3 {
	some c1, c2: Colegio, p: Persona | 
		#(c1.titulares) = 2 and
		#(c1.suplentes) = 2 and
		suplenteATitular[c1, c2, p]		
} for 8

// el colegio tiene el maximo de titulares antes de hacer el intercambio.
run suplenteATitularCasoNoExito {
	some c1, c2: Colegio, p: Persona | 
		#(c1.titulares) = 3 and
		#(c1.suplentes) = 3 and
		suplenteATitular[c1, c2, p]
} for 8

// el colegio tiene solo 1 suplente y ése es la persona que se quiere cambiar.
run suplenteATitularCasoNoExito1 {
	
}

// la persona no es siquiera miembro del colegio
