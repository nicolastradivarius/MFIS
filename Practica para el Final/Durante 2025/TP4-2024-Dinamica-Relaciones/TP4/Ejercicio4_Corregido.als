open util/ordering[Situacion]

sig Filosofo {
	izquierda: one Tenedor,
	// cambiamos el multiplicador de 'lone'
	derecha: one Tenedor
}

sig Tenedor { }

sig Situacion {
	// cambiamos la multiplicidad para que cada filosofo pueda tener tenedores (max. 2)
	comoEstan: Filosofo  -> set Tenedor 
}

// Todos los filosofos y los tenedores estan ubicados en una sola mesa redonda
fact { 
	all f: Filosofo | #Filosofo = #(f.^(izquierda.(~derecha))) 
}

fact "hay al menos dos filosofos y la cantidad de tenedores equivale a la de filosofos" {
	#Filosofo = #Tenedor and #Filosofo >= 2
}

fact "un mismo tenedor no esta en ambos lados del filosofo" {
	no izquierda & derecha
}

fact "no hay dos filosofos con el mismo tenedor del mismo lado" {
	all disj f1, f2: Filosofo |
		(f1.derecha & f2.derecha = none) and
		(f1.izquierda & f2.izquierda = none)
}

fact "Los filosofos solo pueden sostener los tenedores que esten a su alcance" {
	all s: Situacion, f: Filosofo |
		f.(s.comoEstan) in f.(derecha+izquierda)
}


fact "Los tenedores no pueden estar en posesion de mas de un filosofo a la vez" {
	no s: Situacion, disj f1, f2: Filosofo, t: Tenedor |
		(f1->t) in (s.comoEstan) and
		(f2->t) in (s.comoEstan)
}

run default {some comoEstan} for exactly 5 Filosofo, 5 Tenedor, 10 Situacion

run pensando {
	some s: Situacion | no Filosofo.(s.comoEstan)
} for 10

----------- (c) ---------------

// (iii)
fact init {
	// al inicio todos los filosofos estan pensando (sin tenedores)
	no Filosofo.(first.comoEstan)
}


// (iv)
fact traces {
	all s1: Situacion - last | let s2 = s1.next |
		tomarTenedor[s1, s2] or
		soltarTenedores[s1, s2] or
		// necesario para no forzar que en cada cambio de estado se produzca una
		// toma de tenedor, o soltarlos.
		hacerNada[s1, s2]
}

// (ii) Un filósofo f puede tomar uno de los dos tenedores que se encuentran a su alcance en el
// estado s. Para que la acción sea posible el tenedor debe estar disponible.
// Si no se permite que dos filosofos posean el mismo tenedor, entonces no hace falta
// controlar la ultima oracion, porque si el tenedor esta tomado, no podra ser tomado por otro
pred tomarTenedor[s1, s2: Situacion] {
	some f: Filosofo, t: Tenedor |
		( (f->t) not in s1.comoEstan) and
		(s2.comoEstan = s1.comoEstan + (f->t))
}

pred soltarTenedores[s1, s2: Situacion] {
	some f: Filosofo, disj t1, t2: Tenedor |
		( (f->t1) + (f->t2) in s1.comoEstan) and
		(s2.comoEstan = s1.comoEstan - (f->t1) - (f->t2))
}

// Determina si la situacion siguiente es igual a la actual
pred hacerNada[s1, s2: Situacion] {
	s1.comoEstan = s2.comoEstan
}

// Determina si el filosofo esta comiendo en una dada situacion: tiene o no dos tenedores.
pred estaComiendo[f: Filosofo, s: Situacion] {
	#(f.(s.comoEstan)) = 2
}

// no tiene tenedores => esta pensando
pred estaPensando[f: Filosofo, s: Situacion] {
	#(f.(s.comoEstan)) = 0
}

run tomarTenedorCasoExito1 {
	some s: Situacion - last | tomarTenedor[s, s.next]
} for 5

run soltarTenedorCasoExito1 {
	some s: Situacion - last | soltarTenedor[s, s.next]
} for 5

// Si un filosofo tenia sus tenedores y luego dejo de tenerlos, fue por la operacion de soltar.
check tenedoresSoltadosEnAlgunEstado {
	// para todos los posibles filosofos y posibles tenedores
	all f: Filosofo, disj t1, t2: Tenedor |
		// si existe una situacion donde el filosofo tenia los tenedores, y otro posterior
		// donde dejo de tenerlos
		(some s1: Situacion - last, s2: nexts[s1] |
			(f->t1)+(f->t2) in s1.comoEstan and
			(f->t1)+(f->t2) not in s2.comoEstan
		) implies
			// entonces existen situaciones donde se efectuo la operacion de soltar
			(some s3: Situacion - last | let s4 = s3.next | soltarTenedores[s3, s4])
} for 9

run todosLosFilosofosEnLaSituacion {
	some s: Situacion - last | (s.comoEstan).Tenedor = Filosofo
} for exactly 5 Filosofo, 5 Tenedor, 10 Situacion
// para un scope de 5 no encuentra instancias, para uno de 6 cicla


---------- (d) -----------

// Este predicado es incorrecto porque el hecho de que haya filosofos que no esten comiendo
// (ergo estan pensando) no significa que haya un deadlock.
pred nadiePuedeComer1[s: Situacion] {
	all f: Filosofo | not estaComiendo[f, s]
}


pred nadiePuedeComer2[s: Situacion] {
	// los filosofos de la situacion son todos los filosofos de la mesa.
	// si son todos, se llego a un interbloqueo, ya que para que algun filosofo pueda comer
	// necesariamente debe haber otros pensando (sin tenedores).
	(s.comoEstan).Tenedor = Filosofo
}

pred nadiePuedeComer3[s: Situacion] {
	// todos los filosofos...
	all f: Filosofo |
		// tienen exactamente un tenedor en la situacion s
		one t: Tenedor | (f->t) in s.comoEstan
}

// Este predicado es incorrecto porque hay casos donde la situacion es normal y 
// simplemente se repite en las siguientes situaciones.
pred nadiePuedeComer4[s: Situacion] {
	// todas las situaciones siguientes a s son iguales a s
	all s2: nexts[s] | s2.comoEstan = s.comoEstan
}

run nadiePuedeComerCasoExito {
//	some s: Situacion - last | nadiePuedeComer2[s]
	some s: Situacion - last | nadiePuedeComer3[s]
} for exactly 5 Filosofo, 5 Tenedor, 16 Situacion

----- (e) -----

// un deadlock seria el caso en que todos los filosofos tienen un tenedor en su mano y
// estan queriendo tomar el otro para poder comer, pero no pueden porque ya ha sido 
// tomado por otro filosofo, con lo cual se quedan esperando por el resto de los estados.
assert deadlock {
	// existe una situacion...
	some s: Situacion - last |
		// a partir de la cual ningun filosofo puede comer
		all s_sig: nexts[s] + {s} | nadiePuedeComer3[s_sig]
}

check deadlock for exactly 5 Filosofo, 5 Tenedor, 10 Situacion
// Encuentra contraejemplos. La realidad es que no siempre se va a llegar a un interbloqueo
// PAra eso se tienen que dar ciertas condiciones en simultaneo. Lo que vamos a hacer es
// probar que si se llego a una situacion en la que nadie puede comer, entonces se llego
// a un interbloqueo y perdurara por el resto de las situaciones.

assert deadlock2 {
	some s: Situacion - last |
		nadiePuedeComer3[s] implies
			(all ssig: nexts[s] | nadiePuedeComer3[ssig])
}

check deadlock2 for exactly 5 Filosofo, 5 Tenedor, 16 Situacion
// No encuentra contraejemplos.
