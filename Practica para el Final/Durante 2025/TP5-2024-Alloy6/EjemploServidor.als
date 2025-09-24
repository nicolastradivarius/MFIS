sig Servidor {}
var sig FueraLinea in Servidor {}
sig Cliente { 
	var conectado_a: lone Servidor - FueraLinea
}

fact {no FueraLinea and no conectado_a}

run default {} for 5 Servidor, 5 Cliente, 2 steps
