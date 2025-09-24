/*
Indicar nombre, apellido, estado civil y ciudad natal de cada uno de los cuatro compradores
*/

some sig Comprador {
	nombre: one Nombre,
	apellido: one Apellido,
	estadocivil: one EstadoCivil,
	ciudadnatal: one CiudadNatal
}


some sig Nombre {}

some sig Apellido {}

some sig EstadoCivil {}

some sig CiudadNatal {}


one sig Silvio, Diego, Vicente, Carlos extends Nombre {}

one sig Conte, Duarte, Sosa, Valdez extends Apellido {}

one sig Soltero, Casado, Viudo, Divorciado extends EstadoCivil {}

one sig Darregueira, Viedma, Cabildo, Saldungaray extends CiudadNatal {}


run default {} for 4

-----------------------------------------------------------------------

fact "hay cuatro compradores" {
	#Comprador = 4
}

fact "todos los compradores tienen atributos distintos" {
	all disj c1, c2: Comprador | 
		(c1.nombre != c2.nombre) and
		(c1.apellido != c2.apellido) and
		(c1.estadocivil != c2.estadocivil) and
		(c1.ciudadnatal != c2.ciudadnatal)
}

fact "Carlos enviudo" {
	one c: Comprador | (c.nombre in Carlos) and (c.estadocivil in Viudo)
}

fact "la inicial del apellido coincide con la inicial de la ciudad natal" {
	all c: Comprador | 
		(c.apellido in Conte implies c.ciudadnatal in Cabildo) and
		(c.apellido in Duarte implies c.ciudadnatal in Darregueira) and
		(c.apellido in Sosa implies c.ciudadnatal in Saldungaray) and
		(c.apellido in Valdez implies c.ciudadnatal in Viedma)
}

fact "ninguno posee la misma inicial en su nombre, apellido o estado civil" {
	noCoincideNombreApellido[] and 
	noCoincideNombreEstadoCivil[] and
	noCoincideApellidoEstadoCivil[]
}

fact "Vicente se divorcio de la misma mujer que enviudo el que nacio en Saldungaray" {
	some disj c1, c2: Comprador |
		(c1.nombre in Vicente) and
		(c1.estadocivil in Divorciado) and
		(c2.estadocivil in Viudo) and
		(c2.ciudadnatal in Saldungaray)		
}

pred noCoincideNombreApellido[] {
	all c: Comprador | 
		(c.nombre in Silvio implies c.apellido not in Sosa) and
		(c.nombre in Diego implies c.apellido not in Duarte) and
		(c.nombre = Vicente implies c.apellido != Valdez) and
		(c.nombre = Carlos implies c.apellido not in Conte)
}

pred noCoincideNombreEstadoCivil[] {
	all c: Comprador | 
		(c.nombre in Silvio implies c.estadocivil not in Soltero) and
		(c.nombre in Diego implies c.estadocivil not in Divorciado) and
		(c.nombre = Vicente implies c.estadocivil != Viudo) and
		(c.nombre = Carlos implies c.estadocivil not in Casado)
}

pred noCoincideApellidoEstadoCivil[] {
	all c: Comprador | 
		(c.apellido in Sosa implies c.estadocivil not in Soltero) and
		(c.apellido in Duarte implies c.estadocivil not in Divorciado) and
		(c.apellido = Valdez implies c.estadocivil not in Viudo) and
		(c.apellido = Conte implies c.estadocivil not in Casado)
}
