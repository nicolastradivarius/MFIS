/*
sig Bicicleta { 
	rodado: one Rodado, 
	modulo: some ModuloCambios 
} 

sig BMX, Playera, MountainBike extends Bicicleta {} 

abstract sig Rodado {} 

one sig Chico, Mediano, Grande in Rodado {} 

abstract sig ModuloCambios {} 

one sig Tres, Seis, Doce extends ModuloCambios {}
*/

----------------- Corrección del modelo -----------------

// se hace abstracta la signatura para no tener átomos propios (más allá de
// los de las signaturas que la extienden)
abstract sig Bicicleta { 
	rodado: one Rodado, 
	// se cambia "some" por "set" para permitir biciceltas sin módulos.
	modulos: set ModuloCambios 
} 

sig BMX, Playera, MountainBike extends Bicicleta {} 

abstract sig Rodado {} 

// se cambia el "in" por "extends" para garantizar que los conjuntos sean disjuntos.
one sig Chico, Mediano, Grande extends Rodado {} 

abstract sig ModuloCambios {} 

// se elimina la restricción "one" para permitir múltiples módulos de cambios
sig Tres, Seis, Doce extends ModuloCambios {}


----------------- (a) -----------------

// Validación del modelo.

// Cada bicicleta posee un rodado, que es chico, mediano o grande.
// Encuentra contraejemplos en los que:
// 	- una bicicleta tiene un rodado "Rodado$0" desconocido.
// 	- también se percibe que un mismo rodado es de más
//		de un tipo a la vez, como de Mediano y Grande.
check cadaBiciTieneUnRodado {
	all b: Bicicleta | 
		one b.rodado and
		(b.rodado in Chico+Mediano+Grande)
} for 8

// Todo rodado es de un solo tipo.
// Encuentra contraejemplos en los que un rodado es de varios tipos.
check rodadoUnSoloTipo {
/*
	no Chico & Mediano and
	no Chico & Grande and
	no Mediano & Grande and
	no Chico & Mediano & Grande
*/
}	

// Toda bicicleta es de un tipo: playera, BMX o Mountain Bike.
// Encuentra contraejemplos, donde una bicicleta es de un tipo desconocido.
check bicicletaTipo {
	Bicicleta = Playera + BMX + MountainBike
}

// Algunas bicicletas tienen módulos de cambios.
// No encuentra instancias, si algunas bicicletas tienen modulos, algunas no.
// Sin embargo esto no se respeta.
run bicicletaSinModulos {
	some b: Bicicleta | no b.modulos
} for 9

// Cada módulo de cambios puede tener tres, seis o doce cambios. Válido.
check moduloCambios {
	ModuloCambios = Tres + Seis + Doce
} for 9

// Una bicicleta puede tener múltiples modulos de cambios.
// Noto que cuando se establece la restricción de cardinalidad en 4 o más,
// ya no es posible encontrar instancias. Cuando se establece en 3, siempre
// serán Tres, Seis y Doce, sin existir combinaciones de ellas. Esto se 
// puede deber a que las signaturas se definieron como singleton.
check bicicletaMultiplesModulos {
	some b: Bicicleta | #b.modulos = 3
}


---------------- (b) ----------------

pred tiene18cambios[b: Bicicleta] { 
	((#b.modulos = 4) and (#(b.modulos & Seis) = 2) and (#(b.modulos & Tres) = 2)) or 
	((#b.modulos = 5) and (#(b.modulos & Seis) = 1) and (#(b.modulos & Tres) = 4)) or 
	((#b.modulos = 6) and (b.modulos in Tres)) 
}

run tiene18cambios for 20

run bicicletaConModulos {
	some b: Bicicleta | #b.modulos = 3
} for 12

