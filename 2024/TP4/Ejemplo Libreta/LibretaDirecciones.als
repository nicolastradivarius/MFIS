
open util/ordering[Libro] as lib

sig Direccion, Nombre { }

sig Libro {
	anotaciones: Nombre -> Direccion
	}


pred init[l:Libro]{  no l.anotaciones}
fact{init[lib/first]}

pred agregar [b, b': Libro] {
	some n:Nombre, d:Direccion |
		n-> d !in b.anotaciones and
   		b'.anotaciones = b.anotaciones + n->d
	}

pred borrar [b, b': Libro] {
	some n:Nombre, d:Direccion |
		n-> d in b.anotaciones and
		b'.anotaciones = b.anotaciones - n->d
	}

pred corregir [b,b': Libro]  {
	some n:Nombre, disj d1,d2:Direccion |
		n-> d1 in b.anotaciones and
		n-> d2 !in b.anotaciones and
		b'.anotaciones = b.anotaciones - n->d1 + n->d2
	}


fact traces {all lib:Libro-lib/last | 
			let libSig = lib.next |
				agregar[lib,libSig] or
				borrar[lib,libSig] or
				corregir[lib,libSig] 
}

------------- *** realizen comandos para validar el modelo dadod *** --------------------------




--------------    **Propiedades simples para validar**

-- Probamos si se satisface que para corregir una entrada en el libro debe haberse agredado antes
assert modificarsiagreguejustoantes{ all lib:Libro-lib/first -lib/last | corregir[lib,lib.next] implies agregar[lib.prev, lib] }
-- la formulacion dice que debe agregarse justo en el estado anterior.
check modificarsiagreguejustoantes for 5

-- corregimos para formulacion de la propiedad para que quede bien definida

assert modificarsiagregue{ all lib:Libro-lib/first -lib/last | corregir[lib,lib.next] implies some libPrev:lib.(^prev)  | agregar[libPrev, libPrev.next] }

check modificarsiagregue for 5

