/*
Este modelo está basado en el siguiente video:
https://youtu.be/oTP0IgSRct0
*/

sig Bicicleta {
	rod: one Rodado,
	// algunas bicicletas tienen modulos de cambios
	mod: set ModuloCambios
}

sig BMX, Playera, MountainBike extends Bicicleta {} 

abstract sig Rodado {}

one sig Chico, Mediano, Grande extends Rodado {} 

abstract sig ModuloCambios {}

sig Tres, Seis, Doce extends ModuloCambios {}


-------------------- Restricciones --------------------


fact "las bicicletas son de tipo BMX, Playera o MountainBike" {
	Bicicleta = BMX+Playera+MountainBike
}

fact "no hay modulos de bicicletas que no estén aunados a alguna bicicleta" {
	no m: ModuloCambios | no (mod.m)
}

fact "las bicicletas BMX no poseen cambios" {
	no (BMX.mod)
}

fact "las bicicletas MountainBike tienen cambios" {
	(some MountainBike implies some MountainBike.mod)
}

fact "las bicicletas playeras se encuentran disponibles en rodado chico o mediano" {
	(some Playera implies Playera.rod in Chico+Mediano)
}

fact "las bicicletas BMX solo se fabrican en rodado chico" {
	(some BMX implies BMX.rod in Chico)
}

fact "el rodado de las bicicletas mountain bike es mediano o grande" {
	(some MountainBike implies MountainBike.rod in Mediano+Grande)
}

fact "las bicicletas playeras chicas con cambios tienen 3 cambios" {
	all b: Bicicleta | 
		((b in Playera) and (b.rod in Chico) and (some b.mod)) implies tiene3cambios[b]
}

fact "las bicicletas playeras medianas con cambios tienen un total de 3 o 6 cambios" {
	all b: Bicicleta | 
		((b in Playera) and (b.rod in Mediano) and (some b.mod)) implies
			(tiene3cambios[b] or tiene6cambios[b])
}

fact "las bicicletas mountain bike medianas tienen un total de 3, 6 o 12 cambios" {
	all b: Bicicleta | 
		((b in MountainBike) and (b.rod in Mediano)) implies
			(tiene3cambios[b] or tiene6cambios[b] or tiene12cambios[b])
}

fact "las bicicletas mountain bike grandes tienen un total de 6 o 12 cambios" {
	all b: Bicicleta | 
		((b in MountainBike) and (b.rod in Grande)) implies
			(tiene6cambios[b] or tiene12cambios[b])
}

-------------------- Predicados y funciones --------------------


pred tiene3cambios[b: Bicicleta] {
	(b.mod in Tres) and (one b.mod)
}

pred tiene6cambios[b: Bicicleta] {
	((one b.mod) and (b.mod in Seis)) or
	((#(b.mod) = 2 and (b.mod in Tres)))
}

pred tiene12cambios[b: Bicicleta] {
	((one b.mod) and (b.mod in Doce)) or
	((#(b.mod) = 2) and (b.mod in Seis)) or
	((#(b.mod) = 3) and (#(b.mod & Seis) = 1) and (b.mod in Seis+Tres)) or
	((#(b.mod) = 4) and (b.mod in Tres))
}

pred tiene18cambios[b: Bicicleta] {
	((#b.mod = 4) and (#(b.mod & Seis) = 2) and (#(b.mod & Tres) = 2)) or 
	((#b.mod = 5) and (#(b.mod & Seis) = 1) and (#(b.mod & Tres) = 4)) or 
	((#b.mod = 6) and (b.mod in Tres))
}

pred poseeMenorCantCambios[b: Bicicleta] {
	// si la bici es de tipo BMX entonces no puede tener cambios
	// directamente decimos que si es BMX entonces el predicado es automaticamente falso.
	(no b & BMX) and
	(
		// si la bici es de tipo Playera Chica o Mediana, entonces tiene máximo 3 cambios
		(some (b & Playera) and tiene3cambios[b]) or
		// si la bici es de tipo MountainBike Mediana, entonces tiene máximo 3 cambios
		(some (b & MountainBike) and (b.rod in Mediano) and tiene3cambios[b]) or
		// si es MountainBike Grande, entonces como máximo tiene 6 cambios
		(some (b & MountainBike) and (b.rod in Grande) and tiene6cambios[b])
	)
}

// determina si el rodado de b1 es igual o más chico que el de b2
pred noSuperaRodado[b1, b2: Bicicleta] {
	((b1.rod in Chico) and (some b2.rod)) or
	((b1.rod in Mediano) and (b2.rod in Mediano+Grande))
}

// determina si la cantidad de cambios que tiene b1 es menor o igual que la de b2
pred noSuperaCambios[b1, b2: Bicicleta] {
	#(b1.mod) <= #(b2.mod)
}

-------------------- Instancias --------------------

run tiene18cambiosCasoExito {
	some b: Bicicleta | tiene18cambios[b]
} for 6

// no encuentra instancias porque el predicado no permite que una bici tenga 12 cambios
run biciConDoceCambiosTiene18Cambios {
	some b: Bicicleta | some (Doce & b.mod) and tiene18cambios[b]
} for 9

run cuatroBicis {#Bicicleta = 4} for 5

run playeraConCambiosQueNoSeanTres {
	some b: Playera | b.rod in Chico and b.mod not in Tres
} for 8

run default {} for 4



-------------------- Modelado de dinámica --------------------


/*
(i) Añadir un módulo de cambios a una bicicleta. Esta accion está disponible solo para bicicletas
de rodado mediano que posean la menor cantidad de cambios posible (en funcion de su tipo).
*/

pred agregarModuloCambios[bi, bf: Bicicleta, m: ModuloCambios] {
	// Precondiciones:
	-- la bicicleta es de rodado mediano
	(bi.rod in Mediano) and
	-- la bicicleta posee la menor cantidad de cambios posible (en función de su tipo)
	poseeMenorCantCambios[bi] and
	-- el modulo de cambios no estaba previamente agregado a la bicicleta
	(m not in bi.mod) and
	// Postcondiciones
	-- la bicicleta nueva tiene el nuevo modulo
	(bf.mod = bi.mod + m) and
	// Condicion de marco
	-- el rodado de la bicicleta sigue siendo el mismo
	(bf.rod = bi.rod) and
	-- el tipo de bicicleta sigue siendo el mismo
	(some bi & BMX implies some bf & BMX) and // irrelevante porque las BMX no tienen cambios ni estan disponibles en rodado mediano
	(some bi & Playera implies some bf & Playera) and
	(some bi & MountainBike implies some bf & MountainBike)
}

run agregarModuloCambiosCasoExito1 {
	some disj b1, b2: Bicicleta, m: ModuloCambios | agregarModuloCambios[b1, b2, m]
} for 4

// el modulo de cambios es de 3.
// podría ser una mountainbike mediana inicialmente con 3 cambios, y finalmente con 6
run agregarModuloCambiosCasoExito2 {
	some disj b1, b2: Bicicleta, m: ModuloCambios | 
		(m in Tres) and agregarModuloCambios[b1, b2, m]
} for 8

// la bicicleta sobre la que se quiere agregar el módulo, es una bicicleta con 6 cambios.
// pensar qué tipo de bicicleta puede tener 6 cambios... una MountainBike GRANDE
run agregarModuloCambiosCasoNoExito1 {
	some disj b1, b2: Bicicleta, m: ModuloCambios |
		tiene6cambios[b1] and agregarModuloCambios[b1, b2, m]
} for 49

// la bicicleta tiene más modulos luego de habersele agregado uno
run agregarModuloCambiosCasoNoExito2 {
	some disj b1, b2: Bicicleta, m: ModuloCambios |
		tiene3cambios[b1] and tiene12cambios[b2] and agregarModuloCambios[b1, b2, m]
} for 10

// la bici es bmx
run agregarModuloCambiosCasoNoExito3 {
	some disj b1, b2: Bicicleta, m: ModuloCambios |
		(b1 in BMX) and agregarModuloCambios[b1, b2, m]
} for 10

// el modulo de cambios es de 12.
// si la bici fuera playera mediana, solo puede tener 3 o 6 cambios.
// si fuera mountainbike mediana, solo puede tener 3, 6 o 12 cambios; si le agrego un modulo de 12
// a los cambios que ya tiene, por seguro me paso de 12.
run agregarModuloCambiosCasoNoExito4 {
	some disj b1, b2: Bicicleta, m: ModuloCambios |
		(m in Doce) and agregarModuloCambios[b1, b2, m]
} for 15



/*
(ii) Cambiar la cadena de una bicicleta por la de otra. Esta accion es posible si el
rodado de la bicicleta que recibira la cadena no supera el rodado de la bicicleta
que la proporciona. Ademas, la cantidad total de cambios de la bicicleta que
recibe la cadena debera ser menor que la cantidad total de cambios de la bicicleta
que la proporciona. Por ultimo, si la bicicleta que proporciona la cadena posee
el mismo rodado que la que la recibe, la cantidad total de cambios de la bicicleta
que la recibe pasara a ser el mınimo valor posible (en funcion de su tipo)
*/

// cambia la cadena de b por la de b2, i.e. b recibe la cadena, b2 la proporciona.
pred cambiarCadena[bi, bf, b2: Bicicleta] {
	// Precondiciones:
	-- el rodado de la bicicleta que recibe la cadena (b1) no supera el de la que la proporciona (b2)
	noSuperaRodado[bi, b2] and
	-- la cantidad total de cambios de la bicicleta que recibe la cadena debe ser menor que la de b2
	noSuperaCambios[bi, b2] and
	// Postcondiciones:
	-- si ambas bicicletas tienen el mismo rodado, entonces la cantidad total de cambios de b
	-- pasará a ser el mínimo posible (en función de su tipo)
	((bi.rod = b2.rod) implies poseeMenorCantCambios[bf]) and
	// Condición de marco:
	-- el rodado de la bicicleta sigue siendo el mismo
	(bi.rod = bf.rod) and
	-- el tipo de bicicleta sigue siendo el mismo
	(some bi & BMX implies some bf & BMX) and
	(some bi & Playera implies some bf & Playera) and
	(some bi & MountainBike implies some bf & MountainBike)
}

run cambiarCadenaCasoExito1 {
	some disj bi, bf, b2: Bicicleta | cambiarCadena[bi, bf, b2]
} for 4 

/*
(iii) Obtener el conjunto de bicicletas de rodado mediano que poseen hasta 6 cambios
en total
*/

fun bicicletasMedianasConHasta6Cambios: set Bicicleta {
	{b: Bicicleta | (b.rod in Mediano) and tiene6cambios[b]}
}

run bicicletasMedianasConHasta6CambiosCasoExito1 {
	some bicicletasMedianasConHasta6Cambios
} for 9
