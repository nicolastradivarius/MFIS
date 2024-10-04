sig Bicicleta {
	rod: one Rodado,
	mod: some ModuloCambios
}

sig BMX, Playera, MountainBike extends Bicicleta {} 

abstract sig Rodado {}

one sig Chico, Mediano, Grande in Rodado {} 

abstract sig ModuloCambios {}

one sig Tres, Seis, Doce extends ModuloCambios {}

// (a) Validación del modelo

run default {}

// las bicicletas tienen solo un modulo de cambios? Falla, tienen varios.
check bicicletaUnSoloModulo {
	all b: Bicicleta | one b.mod
}

// las bicicletas tienen solo un rodado? Se verifica.
check bicicletaUnSoloRodado {
	all b: Bicicleta | one b.rod
}

// existen otros rodados más allá de los mencionados? Sí. Esto hay que corregirlo.
run otrosRodados {
	some r: Rodado | r !in (Chico + Mediano + Grande)
}

// las bicicletas tienen sus propios rodados? Falla, un mismo rodado está en varias bicicletas. Absurdo
check bicicletasTienenSusPropiosRodados {
	all disj b1, b2: Bicicleta | (b1.rod != b2.rod)
}

// existen bicicletas con más de un mismo modulo (en part. de seis)? No, la signatura Seis es singleton
// una bicicleta puede tener varios cambios.
run bicicletaConVariosModulosDeSeis {
	some b: Bicicleta | #(b.mod & Seis) > 1
}

// todas las bicicletas son algunas de las tres mencionadas? No, hay bicicletas que son aparte.
check todasBicicletasSon {
	all b: Bicicleta | (b in BMX + Playera + MountainBike)
}
