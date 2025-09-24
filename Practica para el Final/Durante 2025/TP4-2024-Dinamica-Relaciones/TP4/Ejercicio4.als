sig Filosofo {
	derecha: lone Tenedor,
	izquierda: Tenedor 
}

sig Tenedor { }

sig Situacion {
	comoEstan: Filosofo -> some Tenedor 
}

// Todos los filosofos y los tenedores estan ubicados en una sola mesa redonda
fact { 
	all f: Filosofo | #Filosofo = #(f.^(izquierda.(~derecha))) 
}

// Caso donde un mismo tenedor esta a la izquierda y a la derecha del filosofo
run mismoTenedorEnAmbosLados {
	some f: Filosofo, t: Tenedor | t in f.derecha and t in f.izquierda
}

// Los tenedores no pueden estar en posesion de mas de un filosofo a la vez
check tenedoresEnMuchasManos {
	no s: Situacion, disj f1, f2: Filosofo, t: Tenedor |
		t in f1.(s.comoEstan) and
		t in f2.(s.comoEstan)
} for 9

// Los filosofos solo pueden sostener los tenedores que esten a su alcance
check filosofosConManosCortas {
	all s: Situacion, f: Filosofo |
		f.(s.comoEstan) = f.(derecha+izquierda)
} for 2 Filosofo, 2 Tenedor, 2 Situacion

// La cantidad de tenedores debe coincidir con la cantidad de filosofos 
check mismaCantidadTenedoresFilosofos {
	#Filosofo = #Tenedor
}

// Caso donde falta un tenedor en la mesa.
// No encuentra instancias. A pesar del 'lone' en 'derecha', no es posible que no haya tenedor.
run faltaTenedor {
	some f: Filosofo | no f.derecha
} for 9

