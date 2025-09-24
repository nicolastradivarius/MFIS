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

fact {all disj p1, p2: Persona | p1.dni != p2.dni} 

fact {no disj p1, p2: Persona |
	(some p1.matricula) and 
	(some p2.matricula) and 
	(p1.matricula = p2.matricula)
} 

//fact {all disj c1, c2: Colegio | c1.id != c2.id}

fact {Colegio = (Provincial+Nacional)}

fact {all c: Colegio | no (c.titulares & c.suplentes)}

fact {all c: Colegio | (c.titulares + c.suplentes) in c.miembros} 

fact {all p: Persona | (some (MatriculaC & p.matricula)) implies (p in Contador)} 

fact {all p: Persona | (some (MatriculaA & p.matricula)) implies (p in Abogado)} 

fact {all p: Persona | (some (MatriculaF & p.matricula)) implies (p in Farmaceutico)}

fact {all p1, p2: Persona, c: Colegio | 
	((p1 in c.miembros) and (p2 in c.miembros)) implies 
			(mismaProfesion[p1,p2] and matriculadosParaMismaProfesion[p1,p2])
}

fact {all c: Provincial | (#c.titulares =< 3) and (#c.suplentes =< #c.titulares)} 

fact {all c: Nacional | (#c.titulares < 5) and (#c.suplentes =< 2)} 

pred mismaProfesion[p1, p2: Persona] { 
	(p1+p2 in Contador) or (p1+p2 in Abogado) or (p1+p2 in Farmaceutico) 
}

pred matriculadosParaMismaProfesion[p1, p2: Persona] {
	((some (p1.matricula & MatriculaC)) and (some (p2.matricula & MatriculaC))) or 
	((some (p1.matricula & MatriculaA)) and (some (p2.matricula & MatriculaA))) or 
	((some (p1.matricula & MatriculaF)) and (some (p2.matricula & MatriculaF)))
}


----------- (b) -------------

// añade una persona al conjunto de miembros de un colegio provincial de contadores.
// esta acción es posible siempre y cuando la persona pertenezca al consejo directivo de
// un colegio nacional de contadores.
pred agregarMiembro [c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and 
	(p in c2.miembros) and 
	(c1.titulares in c2.titulares) and 
	(c1.suplentes in c2.suplentes) 
}

run agregarMiembro

/*
Problemas detectados:
- el colegio donde se añade la persona es el mismo átomo. Así es imposible mostrar el
antes y después.
- la persona que se agrega no necesariamente es un contador ni pertenece al consejo 
directivo de otro colegio nacional.
*/

run agregarMiembroCasoExito1 {
	some disj c1, c2: Colegio, p: Persona | agregarMiembro[c1, c2, p]
}

run agregarMiembroCasoNoExito1 {
	some disj c1, c2: Colegio, p: Persona | 
		c1 in Nacional and
		c2 in Provincial and 
		agregarMiembro[c1, c2, p]
}
// Encuentra instancias, con lo cual no se respeta la invariante de que el colegio tiene que
// ser el mismo luego de agregar p.

check agregarMiembroSiempreEncuentraTercerColegio {
	all disj c1, c2: Colegio, p: Persona |
		agregarMiembro[c1, c2, p] implies 
			(some c3: Colegio | 
				c3.id != c1.id and c3.id != c2.id and c3 in Nacional and
				p in c3.(titulares+suplentes)
			)
} 
// encuentra contraejemplos en los que se efectúa el agregado pero no se cumple que
// exista el colegio nacional al cual pertenece la persona.

check agregarMiembroSiempreAgregaContador {
	all disj c1, c2: Colegio, p: Persona |
		agregarMiembro[c1, c2, p] implies (p in Contador)
}
// Encuentra contraejemplos donde se agregan personas que no son contadores.

run agregarMiembroNoMatriculado {
	some disj c1, c2: Colegio, p: Persona |
		no p.matricula and
		agregarMiembro[c1, c2, p]
} for 10


----- (c) ------


// añade una persona al conjunto de miembros de un colegio provincial de contadores.
// esta acción es posible siempre y cuando la persona pertenezca al consejo directivo de
// un colegio nacional de contadores.
pred agregarMiembroV2 [c1, c2: Colegio, p: Persona] {
	// Precondiciones:

	// El colegio es provincial
	(c1+c2 in Provincial) and
	// La persona es Contador
	(p in Contador) and
	// La persona no está previamente en el colegio
	(p not in c1.miembros) and
	// La persona pertenece al consejo de otro colegio nacional
	(some c3: Colegio | 
		c3 in Nacional and
		c3.id != c1.id and 
		p in c3.(titulares+suplentes)
	) and
	
	// Postcondiciones
	
	// La persona se agregó
	(c2.miembros = c1.miembros + p) and
 
	// Invariantes:
	
	// El ID y consejo directivo del colegio es el mismo
	(c1.id = c2.id) and
	(c1.titulares = c2.titulares) and
	(c1.suplentes = c2.suplentes) 
}

------- Validación del nuevo predicado --------

run agregarMiembroV2 for 10

check agregarMiembroV2SiempreAgregaContador {
	all disj c1, c2: Colegio, p: Persona |
		agregarMiembroV2[c1, c2, p] implies (p in Contador)
}

run agregarMiembroV2QueEstaEnMuchosColegios {
	some disj c1, c2: Colegio, p: Persona |
		some disj c3, c4: Colegio |
			c3 != c1 and c3 != c2 and c4 != c1 and c4 != c2 and
			p in c3.miembros and p in c4.miembros and
			agregarMiembroV2[c1, c2, p]
} for 4

check agregarMiembroV2AumentaNumeroMiembros {
	all disj c1, c2: Colegio, p: Persona |
		(#(c1.miembros) = 1 and agregarMiembroV2[c1, c2, p]) implies 
			(#(c2.miembros) = 2)
} for 4

// Intentar agregar un Contador a un colegio de Abogados.
run agregarMiembroV2CasoNoExito1 {
	some disj c1, c2: Colegio, p: Persona |
		(some a: Abogado | a in c1.miembros) and
		agregarMiembroV2[c1, c2, p]
} for 10

// Si no existen colegios nacionales no sería posible agregar al contador
check agregarMiembroV2CasoNoExito2 {
	all disj c1, c2: Colegio, p: Persona |
		no Nacional implies not agregarMiembroV2[c1, c2, p]
} for 10

// El colegio inicialmente está vacío.
// Como todo colegio debe tener al menos un miembro (el titular), no pueden existir colegios
// vacíos.
run agregarMiembroV2CasoNoExito3 {
	some disj c1, c2: Colegio, p: Persona |
		no c1.(miembros+titulares+suplentes) and
		agregarMiembroV2[c1, c2, p]
} for 10


-------- (d) --------

// Obtener el conjunto de abogados o farmaceuticos que son titulares de al menos un colegio
// y suplentes de a lo sumo un colegio.
fun AbogadosFarmaceuticos[]: set Persona {
	{p: Abogado+Farmaceutico | 
		(some c1: Colegio | p in c1.titulares) and
		(lone c2: Colegio | p in c2.suplentes)
	}
}

run AbogadosFarmaceuticosCasoExito {
	some AbogadosFarmaceuticos
}

// Buscar aquellas instancias donde sea vacío.
run AbogadosFarmaceuticosCasoExito2 {
	no AbogadosFarmaceuticos
}

run AbogadosFarmaceuticosCasoExito3MismoColegio {
	one Colegio and some AbogadosFarmaceuticos
}

--------- (e) --------

// realiza el traspaso de un suplente del consejo de un colegio a titular en dicho colegio.
pred suplenteATitular [c1, c2: Colegio, p: Persona] {
	// Precondiciones:
	-- la persona debe ser suplente del colegio
	(p in c1.suplentes) and
	-- la persona no debe formar parte del consejo de otro colegio
	(no c3: Colegio | c3.id != c1.id and p in c3.(titulares+suplentes)) and
	
	// Postcondiciones:
	-- la persona es titular del colegio
	(c2.titulares = c1.titulares + p) and
	-- la persona ya no es suplente del colegio
	(c2.suplentes = c1.suplentes - p) and

	-- el colegio debe contar con al menos un suplente
	(some c2.suplentes)
}

run suplenteATitular 
