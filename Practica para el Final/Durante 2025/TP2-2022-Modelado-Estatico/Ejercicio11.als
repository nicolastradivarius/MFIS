abstract sig Person {
	children: set Person, // hijos
	siblings: set Person // hermanos
}

sig Man, Woman extends Person {}

sig Married in Person {
	spouse: one Married // esposa
}

run default {} for 5

/*
(a) El modelo brindado tiene algunos problemas:
- Una persona puede ser esposa, hija o hermana de si misma.
- Una persona puede tener de hija a otra persona, y al mismo tiempo, ser su hermana.
- No hay una simetria en las relaciones de familia.
- Persona0 tiene de hijo a Persona1, que tiene de hijo a Persona2, que tiene de hijo a Persona0.
- Persona0 y Persona1 estan casadas con Persona2.
- 
*/

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

fact "si una persona es hermana de otra, no puede mantener otro tipo de relación" {
	all p1, p2: Person |
		(p1 in p2.siblings) implies (
			p1 !in p2.children and
			p1 !in p2.spouse and
			p2 !in p1.children and
			p2 !in p1.spouse
		)
}

fact "si una persona es esposa de otra, no puede mantener otro tipo de relación" {
	all p1, p2: Person |
		(p1 in p2.spouse) implies (
			p1 !in p2.siblings and
			p1 !in p2.children and
			p2 !in p1.siblings and
			p2 !in p1.children
		)
}

fact "una persona no puede tener de hijos a los hijos de sus ancestros" {
	// O sea, si A es padre de B, B es padre de C, C es padre de D, entonces D no puede
	// ser padre de B, porque A (ancestro de D) ya es padre de B.
	// Tomo la relación inversa de children = ~children (padres)
	// Tomo la clausura transitiva de esta relación = ^(~children) (ancestros)
	// Para toda persona p, los hijos de p no pueden ser también hijos de algún
	// ancestro de p
	all p: Person | no (p.children & (p.(^(~children))).children)
}


fact "las personas que comparten padres son hermanos entre sí" {
	all disj p1, p2: Person | 
		(some p3: Person | p1+p2 in p3.children)
			implies 
				(p1->p2 + p2->p1 in siblings)
}

// Devuelve los padres de una persona
fun padres[p: Person]: some Person {
	{p2: Person | p in p2.children}
}

fact "ninguna persona puede ser su propio ancestro" {
	// La clausura transitiva de children se interpreta como
	// los "descendientes" de todas las personas. 
	// Por ejemplo, si A->B y B->C estan en children, entonces
	// A->C esta en ^children. El descendiente de A es C.
	// Por lo tanto si un par (p, p) está en ^children, 
	// entonces p sería su propio descendiente.
	all p: Person | (p->p) not in ^children
}

fact "ninguna persona puede tener mas de una madre ni mas de un padre" {
	// para que eso ocurriese, la persona p debería aparecer más de dos
	// veces como segunda componente de las tuplas en la relación children.
	no p: Person | #(children.p) > 2
}

fact "los hermanos de una persona son aquellas que poseen algun padre en comun" {
	// una persona p y sus hermanos "bros" tienen que cumplir la condicion de 
	// compartir padres, es decir, entre los padres de p y los padres de "bros" hay
	// personas que son las mismas.
	all p: Person | all bros: p.siblings | 
		some (children.p & children.bros)
}

fact "la relacion siblings es simetrica" {
	all disj p1, p2: Person | 
		(p1->p2) in siblings implies (p2->p1) in siblings
}

run personaHermanaDeSiMisma {
	some p: Person | (p->p) in siblings
} for 8

// Irregularidad detectada: Woman1 tiene de hijo a Man0, Man0 tiene de hijo a Woman0,
// y Woman1 esta casada con Woman0 (o sea, con un descendiente)
fact "una persona no puede estar casada con un descendiente" {
	// no hay coincidencias entre la esposa de p y los descendientes de p.
	all p: Person | no (p.^children & p.spouse)
}

fact "una persona no puede estar casada con un familiar" {
	all p: Person | 
		(p.spouse not in p.(^(~children)).(^children)) and
		(p.spouse not in p.(^(~children)).(^spouse).children) and
		(p.spouse not in p.(^(~children)).(^spouse).(^(~children)))
}

fact "la relacion spouse es simetrica" {
	all disj p1, p2: Married | (p1->p2) in spouse implies (p2->p1) in spouse
}

fact "una persona no puede estar casada con mas de una persona" {
	all p: Married | #(p.spouse) <= 1
}

run personaConHijoAmbosCasadosConLaMismaPersona {
	some disj p1, p2, p3: Person |
		p2 in p1.children and
		p3 in p1.spouse and
		p3 in p2.spouse
} for 10

run parejasCasadas {
	some Married
} for 5

/*
Irregularidad detectada: una persona esta casada con otra, ambos con hijos casados entre ellos
*/

// Determina si p1 y p2 poseen un ancestro en comun.
pred parientesDeSangre[p1, p2: Person] {
	some p3: Person | p3 in p1.(^(~children)) and p3 in p2.(^(~children))
}
