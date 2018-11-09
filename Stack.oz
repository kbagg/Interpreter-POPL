declare Stack Environment
Stack = {NewCell nil}
Environment = {NewCell nil}

declare
fun {TopStack}
   @Stack.1
end

declare
fun {PutStack Statement}
   Stack := {Append Statement @Stack}
end
   
declare
proc {SemanticStack AST}
   if AST == [nop] then
      {PutStack [[nop] Environment]}
   else
      {SemanticStack AST.2.1}
      {SemanticStack AST.1}
   end
end