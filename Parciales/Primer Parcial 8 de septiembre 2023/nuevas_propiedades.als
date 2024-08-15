/*
 Creo que se debería contemplar la existencia de alumnos que no estén inscritos en
algún curso, de la misma forma que en la Universidad existen alumnos regulares (con
su legajo/libreta al día) que no están inscritos en las materias de algún cuatrimestre,
y quizá, se inscriban en el siguiente. Esto no es aclarado ni en el diagrama ni en la
descripción.

 También se debería restringir que haya cursos sin alumnos, ya que si ningún alumno
se inscribe a un curso, entonces no puede haber docentes dictándolo debido a lo
mencionado a lo último de la descripción, y por lo general, cuando esto sucede,
los cursos directamente se dan de baja y no se dictan.

 También se debería contemplar la posibilidad de que un Alumno pueda ser Docente en
un curso, es decir, que el docente que imparte el curso sea dicho alumno. Éste alumno
no va a contar como Alumno, sino como Docente, para el curso que esté dictando.
Esto significa que si el curso no tiene alumnos inscriptos, por más que su
docente sea un alumno, no debería ser dictado. Esto invalida la existencia de casos
como cursos que tienen un solo Docente y un solo Alumno que resultase ser el mismo.
*/
