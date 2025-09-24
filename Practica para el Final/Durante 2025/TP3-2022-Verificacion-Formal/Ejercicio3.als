

sig Bicicleta {
	rod: one Rodado,
	mod: some ModuloCambios
}

sig BMX, Playera, MountainBike extends Bicicleta {}

abstract sig Rodado {}

one sig Chico, Mediano, Grande in Rodado {}

abstract sig ModuloCambios {}

one sig Tres, Seis, Doce extends ModuloCambios {}

-----------------------

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
-- Encuentra un contraejemplo donde hay rodados que no son ni chicos, ni medianos ni grandes.
-- Ademas, en las mismas instancias se puede observar que hay varios rodados incluidos en
-- un solo atomo. Esto se debe a que los rodados son subconjuntos no necesariamente disjuntos.

run variosRodadosEnUnoSolo {
	some r: Rodado | r in Chico and r in Mediano
}

// Toda bicicleta es de tipo Playera, BMX o MountainBike
check cadaBicicletaDeUnSoloTipo {
	all b: Bicicleta | b in Playera+BMX+MountainBike
}
-- Encuentra bicicletas que son atomos propios de Bicicleta. Se debe a que no es abstracta.

// ALGUNAS bicicletas tienen modulos de cambios.
run bicicletaSinModulos {
	some b: Bicicleta | no b.mod
}
-- No encuentra instancias. Se debe a la keyword 'some' de la relacion 'mod'.

// Cada modulo puede tener 3, 6 o 12 cambios
check tiposDeModulosDeCambios {
	all m: ModuloCambios | m in Tres+Seis+Doce
} for 7
-- El analizador ni siquiera arma la formula para satisfacerla, con lo cual es posible que
-- lo que se quiere checkear ya se esta cumpliendo por la definicion intrinseca del modelo.


