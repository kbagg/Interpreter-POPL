declare Stack
Stack = {NewCell nil}

declare
fun {PopStack}
   local Top in
      Top = @Stack.1
      Stack := @Stack.2
      Top
   end
end

declare
proc {PushStack Statement Environment}
   Stack := {Append [Statement Environment] @Stack}
end

declare
proc {SemanticStack AST}
   local SemanticStackAux Statement Env in
      proc {SemanticStackAux Environment}
	 Statement = {PopStack}.1
	 if Statement == [nop] then
	    {PushStack [nop] Environment}
	 else
	    {PushStack Statement.2.1 Environment}
	    {SemanticStackAux Environment}
	    {PushStack Statement.1 Environment}
	    {SemanticStackAux Environment} 
	 end
      end
      Env = {NewCell nil}
      {PushStack AST Env}
      {SemanticStackAux Env}
   end
end