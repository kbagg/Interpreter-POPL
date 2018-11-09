declare Stack Environment
Stack = {NewCell nil}
Environment = {NewCell nil}

declare
fun {TopStack}
   @Stack.1
end

declare
proc {PutStack Statement}
   Stack := {Append [Statement Environment] @Stack}
end

declare
proc {SemanticStack AST}
   {PutStack AST}
   local SemanticStackAux Statement in
      proc {SemanticStackAux}
	 Statement = @Stack.1.1
	 if Statement == [nop] then
	    skip
	 else
	    {PutStack Statement.2.1}
	    {SemanticStackAux}
	    {PutStack Statement.1}
	    {SemanticStackAux}
	 end
      end
   end
end