sig Persona { }

sig Alumno in Persona { lib: lone Libreta }

sig Docente in Persona { leg: some Legajo }

sig ID {}

sig Codigo, Legajo, Libreta extends ID {}

sig Curso {
	cod: one ID,
	alumnos: some Alumno, 
	docentes: set Docente
}

fact { all disj c1, c2: Curso | c1.cod != c2.cod }

fact { no disj p1, p2: Persona | p1.lib = p2.lib }

fact { #(Curso.docentes) >= 1 }

fact { all c: Curso | c.alumnos != c.docentes }

---- Validamos el modelo ----

// chequeamos que no existen cursos sin docentes.
// no se verifica ya que hay cursos que no están vinculados a docentes.
check no_cursos_sin_docentes {
	no c: Curso | (no c.docentes)
}

// chequeamos que los cursos tengan un código único (no compartido con otros cursos).
// otra forma de verlo es chequear que no haya códigos que estén asociados
// con varios cursos.
// no se verifica porque hay "códigos sueltos" sin estar asociados a un curso.
check cursos_codigos_unicos {
	all id: Codigo | #(cod.id) = 1
}

// chequeamos que los cursos tengan sólamente Códigos como ID, y no Legajos u otro.
// no se verifica ya que hay cursos cuyo código es la libreta de un alumno.
check cursos_solo_codigos {
	Curso.cod in Codigo
}

// chequeamos que los alumnos no puedan ser docentes de un curso.
// no se verifica, ademas hay alumnos que son docentes a la vez.
check alumnos_no_docentes {
	no (Curso.docentes & Alumno)
}

// chequeamos que la cantidad de docentes de cada curso no supere la de alumnos.
// no se verifica.
check cant_docentes_no_supera_cant_alumnos {
	all c: Curso | #(c.docentes) <= #(c.alumnos)
}

// buscamos instancias donde haya personas que no son ni alumnos ni docentes.
run persona_magica {
	some p: Persona | (p & (Alumno + Docente)) = none
}

// buscamos ver si existen cursos que tengan docentes pero no tengan alumnos.
// no encuentra instancias ya que todos los cursos tienen 1 o más alumnos.
run curso_sin_inscriptos {
	some c: Curso | (some c.docentes) and (no c.alumnos)
}

// buscamos ver si existen cursos con alumnos pero sin docentes.
// se encuentran instancias.
// esta búsqueda no es necesaria porque ya lo cubrimos con un check al inicio.
run curso_sin_docentes {
	some c: Curso | (no c.docentes)
}

// chequeamos si todos los docentes tienen un único legajo asociado.
// no se verifica ya que hay docentes con muchos legajos.
check docentes_legajo {
	all d: Docente | #(d.leg) = 1
}

// buscamos instancias donde haya docentes con libreta.
// no hay, pues para que haya, el docente debe ser alumno.
run docentes_libreta {
	some p: Persona | (p in Docente) and (p not in Alumno) and (some p.lib)
}

// chequeamos si los legajos corresponden a un único docente.
// no se verifica porque hay docentes con multiples legajos.
// este chequeo es el mismo que el de docentes_legajo.
check legajo_unico {
	all disj l1, l2: Legajo | (leg.l1 != leg.l2)
}

// ídem con los códigos de cursos.
// sí se verifica por el primer hecho del modelo.
check codigo_unico {
	all disj c1, c2: Codigo | (cod.c1 != cod.c2)
}

// ídem con las libretas de alumnos.
// sí se verifica por el segundo hecho del modelo.
check libreta_unica {
	all disj l1, l2: Libreta | (lib.l1 != lib.l2)
}

// chequeamos que no haya legajos sueltos (sin estar vinculados a un docente).
// no se verifica.
check legajos_sueltos {
	all l: Legajo | (leg.l != none)
}

// buscamos una instancia con alumnos sin libreta.
// encuentra instancias, algunas donde el alumno es un docente con legajo,
// y otras donde efectivamente es un alumno sin libreta.
run alumno_sin_libreta {
	some a: Alumno | (no a.lib)
}

// buscamos instancias donde haya alumnos que no se inscribieron en cursos
run alumnos_sin_curso {
	some a: Alumno | (no alumnos.a)
}

// buscamos alumnos que se hayan inscripto en más de un curso
run alumnos_multiples_cursos {
	some disj c1, c2: Curso | some (c1.alumnos & c2.alumnos)
}

run default {}
