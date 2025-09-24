sig Candidato { }

one sig Alejo, Luca, Carlos, David in Candidato { }

one sig Maria {
	alto: set Candidato,
	moreno: set Candidato,
	buenmozo: set Candidato
}

run default {} for 4

run {no Maria.alto and no Maria.moreno and no Maria.buenmozo} for 6

/*
Hay cuatro hombres y una mujer llamada Maria.
Maria puede tener de candidatos a alguno de los cuatro hombres, a varios de ellos o a 
candidatos que no se correspondan con los cuatro mencionados. Puede tener ninguno tmb.

(c) La situacion descrita no se corresponde con lo mostrado por las instancias.
- Hay situaciones donde en un mismo candidato estan incluidos Alejo, Luca, etc.
- Hay candidatos que no son alguno de los cuatro mencionados.
- Hay situaciones donde Maria no tiene candidato alguno
*/

fact "Maria tiene cuatro candidatos y estos son los mencionados" {
	(Candidato = Alejo + Luca + Carlos + David) and
	(some Maria.alto and some Maria.moreno and some Maria.buenmozo) and
	(#Candidato = 4)
}

fact "Sólo tres de los hombres son altos, sólo dos son morenos, y sólo uno es buenmozo" {
	(#(Maria.alto) = 3) and
	(#(Maria.moreno) = 2) and
	(#(Maria.buenmozo) = 1)
}

fact "c/u de los cuatro hombres tiene al menos una de las caracteristicas" {
	all c: Candidato | 
		some alto.c or
		some moreno.c or
		some buenmozo.c
}

fact "Alejo y Luca ambos son morenos o ambos no lo son" {
	(Alejo in Maria.moreno iff Luca in Maria.moreno)
}

fact "Luca y Carlos tienen la misma altura" {
	(Luca in Maria.alto iff Carlos in Maria.alto)
}

fact "o bien Carlos es alto o David lo es, pero ambos no lo son" {
	(Carlos in Maria.alto iff David not in Maria.alto)
}
