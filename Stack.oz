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
	 {Browse Statement}
	 if Statement == [nop] orelse Statement == [[nop]] then
	    {PushStack [nop] Environment}
	    {Browse @Stack}
	 else
	    {Browse Statement.2}
	    {PushStack Statement.2 Environment}
	    {Browse @Stack}
	    {SemanticStackAux Environment _}
	    {Browse Statement.1}
	    {PushStack Statement.1 Environment}
	    {Browse @Stack}
	    {SemanticStackAux Environment _} 
	 end
      end
      Env = {NewCell nil}
      {PushStack AST Env}
      {SemanticStackAux Env _}
   end
end

{SemanticStack [[nop] [nop] [nop]]}