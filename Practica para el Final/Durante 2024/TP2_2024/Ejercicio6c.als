sig Conjunto { 
	elementos: set Elemento 
} 

sig Elemento {}


fact "todo elemento pertenece a algún conjunto" {
	all e: Elemento | some elementos.e
}


fact "dos conjuntos con los mismos elementos son el mismo conjunto" {
	all c1, c2: Conjunto | 
		(c1.elementos = c2.elementos) implies (c1 = c2)
}

run default {} for exactly 3 Conjunto, 3 Elemento

// todo conjunto puede expresarse como la unión de otros dos conjuntos.
assert conjuntosCerrados {
	all c1: Conjunto | some disj c2, c3: Conjunto | 
		c1.elementos = c2.elementos + c3.elementos
}

check conjuntosCerrados for 5

fact "todo conjunto puede expresarse como la unión de dos conjuntos" {
	all c: Conjunto | esCerrado[c]
}

/*
Hay un problema al momento de querer probar esta propiedad de manera
directa y sin vueltas. Si solamente buscara satisfacer algo como
all c | some disj c2, c3: Conjunto | c.elementos = c2.elementos + c3.elementos
resultaría en que esta condición se tiene que cumplir para todos los "c",
incluídos c2 y c3. Si se busca que ellos dos la cumplan, habría que buscar
otros dos conjuntos distintos (uno para cada uno, en total cuatro) que, unidos,
formen c2 y c3 respectivamente, pero también se tiene que cumplir la propiedad
para ellos. De esta forma queda claro que se entra en un bucle donde siempre
tiene que existir otro par de conjuntos aparte que ayuden a satisfacer la
condición, rompiendo el scope.
Entiendo que la gracia de probar esta condición es buscar conjuntos disjuntos.
Si se permitiera usar al mismo conjunto como parte de la satisfacción de la
condición, sería tan fácil como decir "la unión de c y el conjunto vacío dan
como resultado a c" y así sucedería en todos los casos. La gracia estaría,
por ejemplo, en tener un conjunto c con cuatro elementos, otros dos con dos
de esos elementos y que unidos den c, otros cuatro con c/uno de esos elementos
y así siguiendo (como si fuera un árbol). Dado que ese problema tiene
características recursivas, establezco que el caso base sea que si un conjunto
no tiene elementos (es vacío) entonces es cerrado, lo cual es así por definición.
Pero si tiene uno solo, también diré que es cerrado, porque sino volvería
a tener el problema del bucle, ya que siempre se necesitaría otro conjunto
con ese elemento para que forme la unión junto al vacío.
*/
pred esCerrado[c: Conjunto] {
	(no c.elementos) or
	(one c.elementos) or
	(
		some c.elementos and 
		some disj c2, c3: Conjunto |
			c2 != c and
			c3 != c and
			c.elementos = c2.elementos + c3.elementos
	)
}

run esCerrado for exactly 5 Conjunto, 3 Elemento

// Determina si c1 está incluído en c2
pred estaIncluido[c1, c2: Conjunto] {
	c1.elementos in c2.elementos
}

run estaIncluido
