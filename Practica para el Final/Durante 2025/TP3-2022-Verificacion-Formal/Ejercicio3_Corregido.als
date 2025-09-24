

abstract sig Bicicleta {
	rod: one Rodado,
	mod: set ModuloCambios
}

sig BMX, Playera, MountainBike extends Bicicleta {}

abstract sig Rodado {}

one sig Chico, Mediano, Grande extends Rodado {}

abstract sig ModuloCambios {}

one sig Tres, Seis, Doce extends ModuloCambios {}

----------------

run default {}

// Cada bicicleta posee UN rodado
check cadaBicicletaPoseeUnRodado {
	all b: Bicicleta | one b.rod
} for 6
-- No encuentra contraejemplos.

// Cada bicicleta posee un rodado, el cual es chico, mediano o grande
check rodadoDeUnTipo {
	all b: Bicicleta |
		b.rod in Chico+Mediano+Grande
} for 6
-- Alloy no logra armar la formula asi que esta propiedad se cumple por definicion.

run variosRodadosEnUnoSolo {
	some r: Rodado | r in Chico and r in Mediano
}
-- No encuentra instancias.

// Toda bicicleta es de tipo Playera, BMX o MountainBike
check cadaBicicletaDeUnSoloTipo {
	all b: Bicicleta | b in Playera+BMX+MountainBike
}
-- No hay formula.

// ALGUNAS bicicletas tienen modulos de cambios.
run bicicletaSinModulos {
	some b: Bicicleta | no b.mod
}
-- Si encuentra instancias.

// Cada modulo puede tener 3, 6 o 12 cambios
check tiposDeModulosDeCambios {
	all m: ModuloCambios | m in Tres+Seis+Doce
} for 7
-- No hay formula.


pred tiene18cambios[b: Bicicleta]{
	((#b.mod = 4) and (#(b.mod & Seis) = 2) and (#(b.mod & Tres) = 2)) or
	((#b.mod = 5) and (#(b.mod & Seis) = 1) and (#(b.mod & Tres) = 4)) or
	((#b.mod = 6) and (b.mod in Tres))
}

// Una bicicleta puede tener múltiples modulos de cambios.
// Noto que cuando se establece la restricción de cardinalidad en 4 o más,
// ya no es posible encontrar instancias. Cuando se establece en 3, siempre
// serán Tres, Seis y Doce, sin existir combinaciones de ellas. Esto se 
// puede deber a que las signaturas se definieron como singleton.
run bicicletaMultiplesModulos {
	some b: Bicicleta | #b.mod = 3
}

run tiene18cambios for 18
