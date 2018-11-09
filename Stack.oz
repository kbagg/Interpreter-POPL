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
   Stack := {Append [[Statement Environment]] @Stack}
end

declare
proc {SemanticStack AST}
   local SemanticStackAux Env in
      proc {SemanticStackAux Environment ?Statement}
	 Statement = {PopStack}.1
	 if Statement == [nop] then
	    {PushStack [nop] Environment}
	 else
	    if Statement.2.2 == nil then
	       {PushStack Statement.2.1 Environment}
	    else
	       {PushStack Statement.2 Environment}
	    end
	    {SemanticStackAux Environment _}
	    {PushStack Statement.1 Environment}
	    {SemanticStackAux Environment _} 
	 end
      end
      Env = {NewCell nil}
      {PushStack AST Env}
      {SemanticStackAux Env _}
   end
end

{SemanticStack [[nop] [nop] [nop]]}
{Browse @Stack}