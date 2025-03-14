one sig Juan, Pedro {}
sig Culpable in univ {}


fact { Juan in Culpable implies Pedro in Culpable } 

assert conclusion { Pedro not in Culpable }

check conclusion

run default {}


------------- (a) -------------

/*
Análisis del modelo:

- El conjunto Culpable puede contener cualquier átomo, ya sea
un número entero, a Juan o a Pedro.
- Por ende, el hecho de que Juan no esté en Culpable, no garantiza
que Pedro tampoco lo esté, ya que ambos están en el conjunto
universal (univ), y así, "Culpable" puede contener a Pedro como
átomo.

*/
