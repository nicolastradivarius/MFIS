/*
Considerar la siguiente situación:

Todos los domingos, Silvio, Diego, Vicente y Carlos compran el diario en el kiosco de Jose.
El ultimo domingo, los cuatro compradores coincidieron en el kiosco al mismo tiempo.
Cuando se iban del kiosco, llegó la esposa de Jose quien comenzó a hacerle preguntas:

(las preguntas serán omitidas y en su lugar se procederá a ir definiendo el modelo)
*/

sig Comprador {
	nombre: one Nombre,
	apellido: one Apellido,
	estadoCivil: one EstadoCivil,
	ciudadNatal: one CiudadNatal
}

abstract sig Nombre {}

abstract sig Apellido {}

abstract sig EstadoCivil {}

abstract sig CiudadNatal {}

one sig Silvio, Diego, Vicente, Carlos extends Nombre {}

one sig Conte, Duarte, Sosa, Valdez extends Apellido {}

one sig Soltero, Casado, Viudo, Divorciado extends EstadoCivil {}

one sig Darregueira, Viedma, Cabildo, Saldungaray extends CiudadNatal {}

---- Restricciones Generales ----

//Hay exactamente cuatro compradores
fact soloCuatroCompradores {#Comprador = 4}

//Cada comprador tiene un nombre, un apellido, una ciudad natal y un estado civil diferente
fact {all disj c1, c2: Comprador |
	(c1.nombre != c2.nombre) and 
	(c1.apellido != c2.apellido) and 
	(c1.ciudadNatal != c2.ciudadNatal) and 
	(c1.estadoCivil != c2.estadoCivil)
}

---- Restricciones Particulares ----

//Carlos enviudó (hay un comprador que se llama Carlos y que es viudo.
fact carlosViudo {one c: Comprador | (c.nombre = Carlos) and (c.estadoCivil = Viudo)}

//La inicial del apellido de cada comprador coincide con la inicial de la ciudad natal de cada uno
fact {all c: Comprador | coincideInicialApellidoCiudadNatal[c]}

//Ningún comprador posee la misma inicial en su nombre, apellido o estado civil (*)
fact {all c: Comprador | 
	noCoincideInicialNombreApellido[c] and
	noCoincideInicialNombreEstadoCivil[c] and
	noCoincideInicialApellidoEstadoCivil[c]
}

//Vicente se divorció de la misma mujer de la que enviudó el que proviene de Saldungaray
fact {one disj c1, c2: Comprador | 
	(c1.nombre = Vicente) and 
	(c1.estadoCivil = Divorciado) and
	(c2.estadoCivil = Viudo) and
	(c2.ciudadNatal = Saldungaray)
}


---- Predicados & Funciones ----

//Determina si para un dado comprador c, su apellido y ciudad natal coinciden en la inicial.
pred coincideInicialApellidoCiudadNatal [c: Comprador] {
	((c.apellido = Conte) implies (c.ciudadNatal = Cabildo)) and
	((c.apellido = Duarte) implies (c.ciudadNatal = Darregueira)) and
	((c.apellido = Sosa) implies (c.ciudadNatal = Saldungaray)) and
	((c.apellido = Valdez) implies (c.ciudadNatal = Viedma))
}
/*
Uso and con implies porque:
	- En caso de que se cumpla la restricción: una de las lineas se hace True por V=>V, entonces las demás se harán True por F=>V o F=>F
	- En caso que no se cumpla la restricción: habrá una de las lineas que se hará False por V=>F, 
	por ejemplo, si el apellido es Conte y la ciudad natal es Viedma; el resto de las lineas se harán True por F=>V o F=>F pero como la primera es False entonces el predicado devuelve False gracias a los and. 
El objetivo es no dejar pasar por alto situaciones. Imaginar qué hubiera pasado si en vez de and hubiera or.
*/

// otra manera es como sigue: usar and y or. Cuando se cumple la restricción, una linea será V y el resto F (por el or, el predicado es V)
// Cuando no se cumple la restricción, todas las lineas son F (por los and) entonces el predicado es F.
/*
	((c.apellido = Conte) and (c.ciudadNatal = Cabildo)) or
	((c.apellido = Duarte) and (c.ciudadNatal = Darregueira)) or
	((c.apellido = Sosa) and (c.ciudadNatal = Saldungaray)) or
	((c.apellido = Valdez) and (c.ciudadNatal = Viedma))
*/


// (*)
/*
Supongase un caso donde Diego se apellida Sosa y está Soltero.
La primer línea va a ser verdadera por F=>F (c.nombre no es Silvio)
La segunda línea es:
	- ¿Es el nombre Diego? True
	- ¿Es su apellido distinto de Duarte y su estado civil distinto de Divorciado? True
	- Entonces V=>V es verdadero
El resto de las líneas son verdaderas y el predicado es verdadero.
De esta forma queda mostrado que este predicado está mal diseñado, porque pasa por alto la igualdad de las
iniciales del apellido Sosa y del estado civil Soltero. Hay que modelarlas por separado.
Además se puede verificar que este caso existe en el modelo (hay que comentar las otras restricciones de modo que
la única que quede sea la que utilizaba este predicado para modelar la restricción) mediante el comando run que esta abajo.
*/

/*
pred noCoincideInicialNombreApellidoEstadoCivil [c: Comprador] {
	((c.nombre = Silvio) implies ((c.apellido != Sosa and c.estadoCivil != Soltero))) and
	((c.nombre = Diego) implies ((c.apellido != Duarte and c.estadoCivil != Divorciado))) and
	((c.nombre = Vicente) implies ((c.apellido != Valdez and c.estadoCivil != Viudo))) and
	((c.nombre = Carlos) implies ((c.apellido != Conte and c.estadoCivil != Casado)))
}


Esta variación tampoco sirve porque ocurre lo mismo de antes:
pred noCoincideInicialNombreApellidoEstadoCivil [c: Comprador] {
	((c.nombre = Silvio) implies (c.apellido != Sosa) implies (c.estadoCivil != Soltero)) and
	((c.nombre = Diego) implies (c.apellido != Duarte) implies (c.estadoCivil != Divorciado)) and
	((c.nombre = Vicente) implies (c.apellido != Valdez) implies (c.estadoCivil != Viudo)) and
	((c.nombre = Carlos) implies (c.apellido != Conte) implies (c.estadoCivil != Casado))
}
*/
run DiegoSosaSoltero{one c: Comprador | c.nombre = Diego and c.apellido = Sosa and c.estadoCivil = Soltero} for 4

pred noCoincideInicialNombreApellido [c: Comprador] {
	((c.nombre = Silvio) implies (c.apellido != Sosa)) and
	((c.nombre = Diego) implies (c.apellido != Duarte)) and
	((c.nombre = Vicente) implies (c.apellido != Valdez)) and
	((c.nombre = Carlos) implies (c.apellido != Conte))
}

pred noCoincideInicialNombreEstadoCivil [c: Comprador] {
	((c.nombre = Silvio) implies (c.estadoCivil != Soltero)) and
	((c.nombre = Diego) implies (c.estadoCivil != Divorciado)) and
	((c.nombre = Vicente) implies (c.estadoCivil != Viudo)) and
	((c.nombre = Carlos) implies (c.estadoCivil != Casado))
}

pred noCoincideInicialApellidoEstadoCivil [c: Comprador] {
	((c.apellido = Sosa) implies (c.estadoCivil != Soltero)) and
	((c.apellido = Duarte) implies (c.estadoCivil != Divorciado)) and
	((c.apellido = Valdez) implies (c.estadoCivil != Viudo)) and
	((c.apellido = Conte) implies (c.estadoCivil != Casado))
}

run solucion {} for 4

/*
Solucion:
	- Un comprador se llama Diego Valdez, es Soltero y nació en Viedma.
	- Otro comprador se llama Carlos Sosa, es Viudo y nació en Saldungaray
	- Otro comprador se llama Vicente Conte, es Divorciado y nació en Cabildo
	- Otro comprador se llama Silvio Duarte, es Casado y nació en Darregueira
*/
