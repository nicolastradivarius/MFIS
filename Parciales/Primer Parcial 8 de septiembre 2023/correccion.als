// hago que Persona sea abstracta para que solamente haya átomos de las signaturas
// que la extienden.
abstract sig Persona { }

// hago que Alumno `extienda` a Persona en lugar que sea un subconjunto, para que
// no se colapse con Docente.
sig Alumno extends Persona {
	// cambio la multiplicidad de `lone` a `one` para que se garantice que un
	// alumno tenga numero de libreta.
	lib: one Libreta
}

// ídem que con Alumno.
sig Docente extends Persona {
	// ídem Libreta, para que un docente no pueda tener múltiples numeros de legajo.
	leg: one Legajo
}

// ídem Persona.
abstract sig ID {}

sig Codigo, Legajo, Libreta extends ID {}

sig Curso {
	// cambio ID por Codigo para que no haya cursos con legajos como código.
	cod: one Codigo,
	// cambiamos la multiplicidad para asegurar que en los cursos haya
	// alumnos y docentes, puesto que no puede haber cursos sin ambos.
	alumnos: some Alumno, 
	docentes: some Docente
}

fact { all disj c1, c2: Curso | c1.cod != c2.cod }

fact { no disj p1, p2: Alumno | p1.lib = p2.lib }

fact { no disj p1, p2: Docente | p1.leg = p2.leg }

fact { #(Curso.docentes) >= 1 }

// cambiamos la forma en que se expresa la restricción para que se adecúe a la
// descripción.
fact { all c: Curso | #(c.docentes) <= #(c.alumnos) }

fact "no códigos sueltos" {
	no c: Codigo | (no cod.c)
}

fact "no libretas sueltas" {
	no l: Libreta | (no lib.l)
}

fact "no legajos sueltos" {
	no l: Legajo | (no leg.l)
}

// este hecho es innecesario debido al cambio de multiplicidad de las relaciones.
fact "curso sin alumnos es curso sin docente" {
	all c: Curso | (no c.alumnos) implies (no c.docentes)
}

---- Validamos el modelo ----

// chequeamos que no existen cursos sin docentes.
// ahora sí se verifica.
check no_cursos_sin_docentes {
	no c: Curso | (no c.docentes)
} for 8

// chequeamos que los cursos tengan un código único (no compartido con otros cursos).
// otra forma de verlo es chequear que cada código esté asociado con un solo curso.
// ahora sí se verifica
check cursos_codigos_unicos {
	all id: Codigo | #(cod.id) = 1
} for 8

// chequeamos que los cursos tengan sólamente Códigos como ID, y no Legajos u otro.
// ahora sí se verifica
check cursos_solo_codigos {
	Curso.cod in Codigo
} for 8

// chequeamos que los alumnos no puedan ser docentes de un curso.
// Ahora es irrelevante porque Alumno y Docente son signaturas disjuntas.
/*
check alumnos_no_docentes {
	no (Curso.docentes & Alumno)
} for 8
*/

// chequeamos que la cantidad de docentes de cada curso no supere la de alumnos.
// sí se verifica.
check cant_docentes_no_supera_cant_alumnos {
	all c: Curso | #(c.docentes) <= #(c.alumnos)
} for 8

// buscamos instancias donde haya personas que no son ni alumnos ni docentes.
// no encuentra, lo cual está bien.
run persona_magica {
	some p: Persona | (p & (Alumno + Docente)) = none
} for 8

// buscamos ver si existen cursos que tengan docentes pero no tengan alumnos.
// no encuentra instancias ya que todos los cursos tienen 1 o más alumnos.
run curso_sin_inscriptos {
	some c: Curso | (some c.docentes) and (no c.alumnos)
} for 8

// buscamos ver si existen cursos con alumnos pero sin docentes.
// No se encuentran instancias.
run curso_sin_docentes {
	some c: Curso | (no c.docentes)
} for 8

// chequeamos si todos los docentes tienen un único legajo asociado.
// ahora sí se verifica.
check docentes_legajo {
	all d: Docente | #(d.leg) = 1
} for 8

// buscamos instancias donde haya docentes con libreta.
// no hay, pues para que haya, el docente debe ser alumno.
run docentes_libreta {
	some p: Persona | (p in Docente) and (p not in Alumno) and (some p.lib)
} for 8

// chequeamos si los legajos corresponden a un único docente.
// ahora se verifica.
// este chequeo es el mismo que el de docentes_legajo.
check legajo_unico {
	all disj l1, l2: Legajo | (leg.l1 != leg.l2)
} for 8

// ídem con los códigos de cursos.
// sí se verifica por el primer hecho del modelo.
check codigo_unico {
	all disj c1, c2: Codigo | (cod.c1 != cod.c2)
} for 8

// ídem con las libretas de alumnos.
// sí se verifica por el segundo hecho del modelo.
check libreta_unica {
	all disj l1, l2: Libreta | (lib.l1 != lib.l2)
} for 8

// chequeamos que no haya legajos sueltos (sin estar vinculados a un docente).
// ahora se verifica.
check legajos_sueltos {
	all l: Legajo | (leg.l != none)
} for 8

// buscamos una instancia con alumnos sin libreta.
// ahora se verifica.
run alumno_sin_libreta {
	some a: Alumno | (no a.lib)
} for 8

// buscamos instancias donde haya alumnos que no se inscribieron en cursos.
// encuentra, ya que permitimos esa posibilidad.
run alumnos_sin_curso {
	some a: Alumno | (no alumnos.a)
} for 8

// buscamos alumnos que se hayan inscripto en más de un curso
// encuentra.
run alumnos_multiples_cursos {
	some disj c1, c2: Curso | some (c1.alumnos & c2.alumnos)
} for 8

// buscamos docentes que impartan más de un curso.
// encuentra.
run docentes_multiples_cursos {
	some d: Docente | #(docentes.d) > 1
} for 8

run default {#Curso = 3 and #Alumno = 3 and #Docente = 2} for 5 but 10 ID
