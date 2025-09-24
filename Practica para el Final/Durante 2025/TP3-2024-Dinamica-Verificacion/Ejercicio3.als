abstract sig Computadora {
	perifericos: set Periferico,
	numInvComp: one NumInv
}

abstract sig Periferico {
	numInvPer: one NumInv
}

sig NumInv {}

sig Notebook, AllInOne, Desktop extends Computadora {}

sig Mouse, Teclado, Monitor extends Periferico {}

// Bloquea la dinamica
/*
fact "toda computadora esta identificada por un numero de inventario" {
	no disj c1, c2: Computadora | c1.numInvComp = c2.numInvComp
}
*/

fact "todo periferico esta identificado por un numero de inventario" {
	all disj p1, p2: Periferico | p1.numInvPer != p2.numInvPer
}

fact "un periferico y una computadora no pueden tener el mismo numero de inventario" {
	all c: Computadora, p: Periferico | c.numInvComp != p.numInvPer
}

// Bloquea la dinamica
/*
fact "no hay un mismo periferico en dos computadoras distintas" {
	all disj c1, c2: Computadora, p: Periferico | 
		(p in c1.perifericos and p in c2.perifericos) implies
			(c1.numInvComp = c2.numInvComp)
}
*/

----- (b) ------

fact "las computadoras desktop tienen al menos un monitor" {
	all c: Desktop | some (c.perifericos & Monitor)
}

fact "las notebooks no tienen mouse ni teclado" {
	all c: Notebook | no (c.perifericos & Mouse) and no (c.perifericos & Teclado)
}

fact "las allinone y desktops tienen al menos un teclado y al menos un mouse" {
	all c: AllInOne + Desktop | 
		some (c.perifericos & Teclado) and
		some (c.perifericos & Mouse)
}

fact "ninguna computadora puede tener mas de cinco perifericos que sean monitores" {
	no c: Computadora | #(c.perifericos & Monitor) > 5
}

run hayDesktops { some Desktop } for 5

run algunaNotebookConMouse {
	some c: Notebook | some p: Mouse | p in c.perifericos
} for 10

check lasDesktopsSiempreTienenMonitor {
	all c: Desktop | some p: Monitor | p in c.perifericos
} for 16

check lasAllInOneSiempreTienenMonitor {
	all c: AllInOne | some p: Monitor | p in c.perifericos
}
// Encuentra contraejemplos y es porque no necesariamente tienen que tener un monitor.


------ (c) ------

// modela el comportamiento de agregar un periferico a una desktop.
// esta accion es posible siempre y cuando posea la misma cantidad de teclados y mouse.
pred agregarPeriferico[c1, c2: Computadora, p: Periferico] {
	-- finalmente la computadora no tiene la misma cantidad de mouses y de teclados
	not(#(c2.perifericos & Mouse) = #(c2.perifericos & Teclado)) and
	-- finalmente el periferico esta agregado a la computadora
	(p in c2.perifericos) and
	-- todos los perifericos que inicialmente tenia la computadora, los tendra finalmente
	(c1.perifericos in c2.perifericos)
}

run agregarPeriferico for 4

/*
Irregularidades detectadas:
- el atomo c1 y c2 son el mismo, con lo cual no hay una clara separacion entre el
"antes" y el "despues" del predicado.
- la cantidad de teclados y mouses no es consistente. Por ejemplo, se agrega un mouse y
finalmente se cuenta con 1 mouse y 2 teclados, lo cual indica que originalmente habia solo
dos teclados y por ende el predicado no deberia haber tenido exito.
*/

check chequeoDeInvariantePerifericos {
	all disj c1, c2: Computadora, p: Periferico |
		agregarPeriferico[c1, c2, p] implies
			(c2.perifericos = c1.perifericos + p)
} for 5
// Encuentra contraejemplos donde la computadora inicialmente no tiene perifericos, y 
// despues tiene otros adicionales al que se agrega.
// Otros contraejemplos son simplemente que no se satisface la igualdad.

run inicialmenteTienePerifericos {
	some disj c1, c2: Computadora, p: Periferico | 
		some c1.perifericos and
		agregarPeriferico[c1, c2, p]
} for 5
// En algunas instancias encontradas, c1 tiene el periferico que se quiere agregar.

// Caso donde inicialmente no tiene la misma cantidad inicial de teclados y mouses.
run agregarPerifericoCasoNoExito {
	some disj c1, c2: Computadora, p: Periferico | 
		#(c1.perifericos & Teclado) > 1 and
		one (c1.perifericos & Mouse) and
		agregarPeriferico[c1, c2, p]
} for 5
// Encuentra instancias cuando no deberia encontrarlas porque es un requerimiento.

// Caso donde el periferico ya estaba agregado en la computadora
run agregarPerifericoCasoNoExito2 {
	some disj c1, c2: Computadora, p: Periferico | 
		(p in c1.perifericos) and
		agregarPeriferico[c1, c2, p]
} for 5
// Encuentra instancias igual. Y ademas, hay otros perifericos adicionales que c1 no tenia.

// AgregarPeriferico version 2.
// modela el comportamiento de agregar un periferico a una desktop.
// esta accion es posible siempre y cuando posea la misma cantidad de teclados y mouse.
pred agregarPerifericoV2[c1, c2: Computadora, p: Periferico] {
	// Precondiciones:
	-- La computadora es de tipo desktop
	(c1 in Desktop) and
	-- El periferico no estaba previamente en la computadora
	(p not in c1.perifericos) and
	-- La computadora posee la misma cantidad de teclados y de mouses.
	(#(c1.perifericos & Teclado) = #(c1.perifericos & Mouse)) and

	// Postcondiciones:
	-- Finalmente p esta incluido en los perifericos
	(c2.perifericos = c1.perifericos + p) and
	
	// Invariantes:
	-- El numero de inventario de la computadora es el mismo
	(c2.numInvComp = c1.numInvComp) and
	-- El tipo de computadora es el mismo
	(c2 in Desktop)
}

run agregarPerifericoV2 for 6

----- (d) -----

// Modela el comportamiento de quitar un monitor de una all-in-one o de una notebook.
// Para que dicha acción pueda realizarse la cantidad de teclados y mouse de la computadora
// original no puede superar (en forma conjunta) su cantidad de monitores. 
// Luego del traspaso, la computadora deberá contar con al menos dos monitores.
pred quitarMonitor[c1, c2: Computadora, p: Periferico] {
	// Precondiciones: 
	-- El periferico es un monitor
	(p in Monitor) and
	-- La computadora es una all-in-one o notebook
	(c1 in AllInOne+Notebook) and
	-- El monitor esta inicialmente en la computadora
	(p in c1.perifericos) and
	-- La cantidad de teclados + mouses inicial no puede superar a la de monitores
	(#(c1.perifericos & (Teclado+Mouse)) <= #(c1.perifericos & Monitor)) and
	
	// Postcondiciones
	-- El monitor finalmente no esta en la computadora
	(c2.perifericos = c1.perifericos - p) and
	-- La computadora cuenta con al menos dos monitores
	(#(c2.perifericos & Monitor) >= 2) and

	// Invariantes
	-- El numero de inventario de la computadora es el mismo
	(c2.numInvComp = c1.numInvComp) and
	-- La computadora sigue siendo una all-in-one o notebook
	(c2 in AllInOne+Notebook)
}

run quitarMonitor for 5

// Caso donde la computadora tiene algun teclado inicialmente.
run quitarMonitorCasoExito2 {
	some disj c1, c2: Computadora, p: Periferico |
		some (c1.perifericos & Teclado) and
		quitarMonitor[c1, c2, p]
} for 6

// Aseguramos que despues de ejecutar el predicado siempre se disminuye en 1 la cantidad
// de monitores.
check quitarMonitorCasoExito3 {
	all disj c1, c2: Computadora, p: Periferico |
		(#(c1.perifericos & Monitor) = 3 and quitarMonitor[c1, c2, p]) implies 
			(#(c2.perifericos & Monitor) = 2)
} for 19

// Caso donde la computadora tiene 2 monitores. Si se quita uno, se viola la postcondicion.
run quitarMonitorCasoNoExito1 {
	some disj c1, c2: Computadora, p: Periferico |
		#(c1.perifericos & Monitor) = 2 and
		quitarMonitor[c1, c2, p]
} for 16
// No encuentra instancias por lo mencionado. Si se quita la clausula correspondiente, 
// encontrara instancias.

// Aseguramos que siempre que la computadora tenga 2 monitores o menos, no sera posible
// satisfacer el predicado
check quitarMonitorCasoNoExito2 {
	all disj c1, c2: Computadora, p: Periferico |
		(#(c1.perifericos & Monitor) <= 2) implies not quitarMonitor[c1, c2, p]
} for 16

----- (e) -----

// Modela el comportamiento de reemplazar un periférico por otro del mismo tipo 
// en una all-in-one.
// Esta acción es posible siempre y cuando el periférico a reemplazar sea un teclado o monitor.
pred reemplazarPeriferico[c1, c2: Computadora, p1, p2: Periferico] {
	(p1 in c1.perifericos) and
	(p2 !in c1.perifericos) and
	(p1 ! in Teclado + Monitor) and
	(c1.perifericos != c2.perifericos)
	(p2 in c2.perifericos)
}

run reemplazarPeriferico for 4

/*
Irregularidades detectadas:
- los dos atomos c1 y c2 son de distinto tipo de computadora, deberian ser el mismo.
- el periferico reemplazante es de diferente tipo al reemplazado.
- no se mantiene invariante la posesion del resto de los perifericos no involucrados.
- el numero de inventario de c1 y c2 difiere, cuando deberia ser el mismo (es invariante)
- uno de los perifericos (el reemplazado) es un mouse.
*/

// Aseguramos que la cantidad de perifericos se mantenga invariante.
check reemplazarPerifericoPreservaCantidad {
	all c1, c2: Computadora, p1, p2: Periferico |
		reemplazarPeriferico[c1, c2, p1, p2] implies
			(#(c1.perifericos) = #(c2.perifericos))
} for 5
// Encuentra contraejemplos, en particular el primero es tal que c2 tiene como periferico
// adicional el "p1" que se supone tiene que reemplazar por "p2".

// Caso donde se busca reemplazar a un teclado o monitor, por un mouse.
run reemplazarPerifericoCasoExito2 {
	some c1, c2: Computadora, p1, p2: Periferico |
		(p2 in Mouse) and
		reemplazarPeriferico[c1, c2, p1, p2]	
} for 6

// Caso donde el numero de inventario de la computadora no se mantiene invariante.
run reemplazarPerifericoCasoNoExito1 {
	some c1, c2: Computadora, p1, p2: Periferico |
		c1.numInvComp != c2.numInvComp and
		reemplazarPeriferico[c1, c2, p1, p2]
} for 5
// Encuentra instancias por lo que esta parte esta mal.

// Caso donde el periferico reemplazante es de distinto tipo que el reemplazado.
run reemplazarPerifericoCasoNoExito2 {
	some c1, c2: Computadora, p1, p2: Periferico |
		(p1 in Teclado implies p2 not in Teclado) and
		(p1 in Monitor implies p2 not in Monitor) and
		reemplazarPeriferico[c1, c2, p1, p2]
} for 5
// Encuentra instancias donde incluso p1 es de tipo Mouse, lo cual no esta permitido.
// Si se restringe que p1 no sea de tipo Mouse, no encuentra instancias.

// Aseguramos que el periferico reemplazado es siempre de tipo Mouse (lo cual esta mal porque
// debe ser un teclado o monitor).
check perifericoAReemplazarEsMouse {
	all c1, c2: Computadora, p1, p2: Periferico |
		reemplazarPeriferico[c1, c2, p1, p2] implies (p1 in Mouse)
} for 19
// No encuentra contraejemplos.

// Caso donde la computadora no es all-in-one.
run reemplazarPerifericoCasoNoExito3 {
	some c1, c2: Computadora, p1, p2: Periferico |
		(c1 not in AllInOne) and
		(c2 not in AllInOne) and
		reemplazarPeriferico[c1, c2, p1, p2]
} for 5
// Encuentra instancias, lo cual indica que el predicado no controla que se le haga el reemplazo
// a una All-In-One.


---- (f) ----

// Modela el comportamiento de reemplazar un periférico por otro del mismo tipo 
// en una all-in-one.
// Esta acción es posible siempre y cuando el periférico a reemplazar sea un teclado o monitor.
pred reemplazarPerifericoV2 [c1, c2: Computadora, p1, p2: Periferico] {
	// Precondiciones:
	-- El periferico a reemplazar esta inicialmente en la computadora.
	(p1 in c1.perifericos) and
	-- La computadora es de tipo All-In-One
	(c1 in AllInOne) and
	-- El periferico a reemplazar es un teclado o monitor
	(p1 in Teclado + Monitor) and
	-- El periferico reemplazante es del mismo tipo que el que se va a reemplazar
	(p1+p2 in Teclado or p1+p2 in Monitor) and
	
	// Postcondiciones:
	-- El periferico reemplazante forma parte de los perifericos de la computadora.
	(c2.perifericos = c1.perifericos - p1) and
	(p2 in c2.perifericos) and
	
	// Invariantes
	-- El resto de los perifericos estan presentes en la computadora
	(c1.perifericos - p1) = (c2.perifericos - p2) and
	-- El numero de inventario de la computadora es el mismo
	(c1.numInvComp = c2.numInvComp)
}

run reemplazarPerifericoV2 for 6


