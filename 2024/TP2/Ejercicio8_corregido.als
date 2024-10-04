// hacemos abstracta a Bicicleta para que no puedan existir otras más allá de las mencionadas
abstract sig Bicicleta {
	rod: one Rodado,
	mod: some ModuloCambios
}

sig BMX, Playera, MountainBike extends Bicicleta {} 

abstract sig Rodado {}

// hacemos que extiendan a Rodado así no existen otros rodados aparte de los mencionados.

sig Chico, Mediano, Grande extends Rodado {} 

abstract sig ModuloCambios {}

// removemos la multiplicidad 'one' para permitir que haya varios modulos de cambios
sig Tres, Seis, Doce extends ModuloCambios {}

// (a) Validación del modelo

run default {}

// las bicicletas tienen solo un modulo de cambios? No, pero está bien porque puede tener varios.
check bicicletaUnSoloModulo {
	all b: Bicicleta | one b.mod
}

// las bicicletas tienen solo un rodado? Se verifica.
check bicicletaUnSoloRodado {
	all b: Bicicleta | one b.rod
}

// no encuentra instancias, por lo que estamos bien.
run otrosRodados {
	some r: Rodado | r !in (Chico + Mediano + Grande)
}

// las bicicletas tienen sus propios rodados? Sigue fallando
check bicicletasTienenSusPropiosRodados {
	all disj b1, b2: Bicicleta | (b1.rod != b2.rod)
}

// existen bicicletas con más de un mismo modulo (en part. de seis)? No, la signatura Seis es singleton
run bicicletaConVariosModulosDeSeis {
	some b: Bicicleta | #(b.mod & Seis) > 1
} for 7

// todas las bicicletas son algunas de las tres mencionadas? Se verifica.
check todasBicicletasSon {
	all b: Bicicleta | (b in BMX + Playera + MountainBike)
}


----------------------------------------


fact "cada bicicleta tiene su propio rodado" {
	all disj b1, b2: Bicicleta | (b1.rod != b2.rod)
}

fact "cada bicicleta tiene su propio modulo de cambios" {
	all disj b1, b2: Bicicleta |  no (b1.mod & b2.mod)
}

fact "no hay rodados de bicicletas que no estén aunados a alguna bicicleta" {
	all r: Rodado | one rod.r
}

fact "no hay modulos de bicicletas que no estén aunados a alguna bicicleta" {
	no m: ModuloCambios | no (mod.m)
}

pred tiene18cambios[b: Bicicleta] {
	((#b.mod = 4) and (#(b.mod & Seis) = 2) and (#(b.mod & Tres) = 2)) or 
	((#b.mod = 5) and (#(b.mod & Seis) = 1) and (#(b.mod & Tres) = 4)) or 
	((#b.mod = 6) and (b.mod in Tres))
}

run tiene18cambiosCasoExito {
	some b: Bicicleta | tiene18cambios[b]
} for 6

// no encuentra instancias porque el predicado no permite que una bici tenga 12 cambios
run biciConDoceCambiosTiene18Cambios {
	some b: Bicicleta | some (Doce & b.mod) and tiene18cambios[b]
} for 9

run cuatroBicis {#Bicicleta = 4} for 5
