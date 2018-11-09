declare Stack Environment
Stack = {NewCell nil}
Environment = {NewCell nil}

declare
fun {TopStack}
   @Stack.1
end

declare
fun {PutStack Statement}
   Stack := {Append [Statement Environment] @Stack}
end

declare
proc {SemanticStack AST}
   {PutStack AST Environment}
   local SemanticStackAux Statement in
      proc {SemanticStackAux}
	 Statement = @Stack.1.1
	 if Statement == [nop] then
	    pass
	 else
	    {PutStack Statement.2.1}
	    {SemanticStackAux}
	    {PutStack Statement.1}
	    {SemanticStackAux}
   end
end