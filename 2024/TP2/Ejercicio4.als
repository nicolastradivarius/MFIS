sig Candidato { } 

one sig Alejo, Luca, Carlos, David in Candidato { } 

one sig Maria {
	alto: set Candidato, 
	moreno: set Candidato, 
	buenmozo: set Candidato 
}

-------------- (a) --------------

/*
El modelo representa una situación en la que María tiene una
serie de candidatos, entre los cuales están Alejo, Luca, Carlos y
David.
*/

-------------- (b) --------------

/*
Las instancias del modelo muestran situaciones en las que:
- Hay candidatos que no son alguno de los cuatro mencionados,
- Un mismo átomo de Candidato representa varios candidatos.
- María tiene preferencias por candidatos que no son alguno de
los cuatro.
*/

-------------- (c) --------------

/*
No se corresponde.
*/

/*
No es necesario porque con el de abajo se define a Candidato.
fact "hay cuatro candidatos" {
	#Candidato = 4
}
*/

fact "los unicos candidatos son los cuatro mencionados" {
	Candidato = Alejo + Luca + Carlos + David
}


-------------- (d) --------------

fact "tres hombres altos, dos morenos, un buenmozo" {
	#alto = 3 and
	#moreno = 2 and
	#buenmozo = 1
}

fact "c/u de los cuatro tiene al menos una caracteristica" {
	all c: Candidato | 
		some alto.c or 
		some moreno.c or 
		some buenmozo.c
}

fact "alejo y luca tienen la misma complexion" {
	// ambos son morenos o ambos no lo son
	(Alejo in Maria.moreno iff Luca in Maria.moreno)
}

fact "luca y carlos tienen la misma altura" {
	// ambos son altos o ambos no lo son
	(Luca in Maria.alto iff Carlos in Maria.alto)
}

fact "o bien Carlos es alto o David lo es, pero ambos no son" {
//	(Carlos in Maria.alto and David !in Maria.alto) or
//	(Carlos !in Maria.alto and David in Maria.alto)
	(Carlos in Maria.alto iff David !in Maria.alto)
}

run default {} for 4

run candidatoDeMaria {
	some c: Candidato | 
		c in Maria.alto and 
		c in Maria.moreno and 
		c in Maria.buenmozo
} for 4
