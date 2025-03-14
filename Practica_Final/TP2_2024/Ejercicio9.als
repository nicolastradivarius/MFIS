abstract sig Person { 
	children: set Person, // hijos 
	siblings: set Person // hermanos
} 

sig Man, Woman extends Person {} 

sig Married in Person { 
	spouse: one Married 
}


run default {}

------------------ (a) ------------------

/*
Análisis de instancias:

- Instancia 1 y 2: 
	Dos mujeres Woman$0 y Woman$1, y un hombre Man$0;
	El Man$0 está casado consigo mismo;
	Woman$1 es hermana de sí misma y tiene de esposo a Man$0;
	su hija es Woman$0, pero desde el punto de vista de Woman$0, Woman$1 es su hermana;
	las relaciones de esposo y hermanos deberían ser simétricas y no lo son;
	todas las relaciones deberían limitar al resto de relaciones para una persona;
	Woman$0 es hija de sí misma;
	Man$0 es esposo e hijo de sí mismo (superposición de relaciones familiares);
*/

run personaCasadoConSiMismo {
	some p: Person | p in p.spouse
}

run personaPrimaDeSiMisma {
	some p: Person | p in p.siblings
}

// p1 tiene de hijo a p2, pero p2 ve a p1 como su hermano o esposo (o incluso hijo).
run hijoQueConfundePadres {
	some disj p1, p2: Person | 
		p2 in p1.children and 
//		p1 in p2.siblings
//		p1 in p2.children
		p1 in p2.spouse
}

run personaConMultiplesRelacionesFamiliares {
	some p: Person | 
		p in p.children and
		p in p.siblings and
		p in p.spouse
}

// p1 es hermano de p2 pero p2 no es hermano de p1
run hermanosQueNoSonPrimos {
	some disj p1, p2: Person | 
		p1 in p2.siblings and
		p2 !in p1.siblings
}

run espososQueNoSonEsposos {
	some disj p1, p2: Person |
		p1 in p2.spouse and
		p2 !in p1.spouse
}

fact "una persona no puede estar casada con sí misma" {
	no p: Married | (p->p) in spouse
}

fact "una persona no puede ser hermana de sí misma" {
	no p: Person | (p->p) in siblings
}

fact "si una persona es hija de otra, no puede mantener otro tipo de relación" {
	all p1, p2: Person |
		(p1 in p2.children) implies (
			p1 !in p2.siblings and
			p1 !in p2.spouse and
			p2 !in p1.siblings and
			p2 !in p1.spouse
		)
}

------------------ (b) ------------------

// determina si p3 es el hijo de p1 y p2 (p1 y p2 son los padres de p3)
pred sonPadres[p1, p2, p3: Person] {
	p3 in p1.children and
	p3 in p2.children
}

// encuentra instancias válidas desde el punto de vista del predicado.
// claramente hay errores, como que p1 también es el hijo de p3.
run sonPadresCasoExito {
	some disj p1, p2, p3: Person | sonPadres[p1, p2, p3]
}

------------------ (c) ------------------

fact "ninguna persona puede ser su propio ancestro" {
	// la clausura transitiva de children se interpreta como
	// los "descendientes" de todas las personas. Si un par
	// (p, p) está en esta relación, entonces p sería su
	// propio descendiente.
	all p: Person | (p->p) not in ^children
//	all p: Person | p not in p.children
}

fact "ninguna persona puede tener más de una madre, ni más de un padre" {
	// para que eso ocurriese, la persona p debería aparecer más de dos
	// veces como segunda componente de las tuplas en la relación children.
	no p: Person | #(children.p) > 2
}

fact "los hermanos de una persona poseen algún padre en común" {
	all p: Person | all bro: p.siblings | 
		some (children.p & children.bro)
}

run buscandoPadres {
	some disj p1, p2, p3: Person | esPadre[p1, p3] and esMadre[p2, p3]
}

run buscandoHermanos {
	some disj p1, p2, p3: Person | some children.p1 and (p2+p3) in p1.siblings
}

pred esPadre[p1, p2: Person] {
	// p1 es padre de p2
	p1 in Man and
	p2 in p1.children
}

pred esMadre[p1, p2: Person] {
	p1 in Woman and
	p2 in p1.children
}
