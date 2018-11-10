\insert 'Unify.oz'
\insert 'SingleAssignmentStore.oz'

declare Stack Count
Stack = {NewCell nil}
Count = {NewCell 1}

declare
fun {NewVar}
   local Var in
      Var = {Append "Var" @Count}
      Count := @Count + 1
      Var
   end
end

{Browse {NewVar}}
{Browse {NewVar}}

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
      proc {SemanticStackAux}
	 local Statement Environment in
	    [Statement Environment] = {PopStack}
	    case Statement
	    of [nop] then
	       {PushStack [nop] Environment}
	    [] [var ident(X) S] then
	       local Var in
		  Var = {NewVar}
		  Environment := {Adjoin @Environment env(X:Var)}
		  {AddToSAS Var}
		  {PushStack S Environment}
		  {SemanticStackAux}
	       end
	    [] [bind ident(X) ident(Y)] then
	       {Unify ident(X) ident(Y) @Environment}
	    [] [bind ident(X) V] then
	       {Unify ident(X) V @Environment}
	    [] [conditional ident(X) S1 S2] then
	       case {Dictionary.get SAS @Environment.X}
	       of literal(true) then {PushStack S1 Environment}
	       [] literal(false) then {PushStack S2 Environment}
	       else {Exception.'raise' variableUnbound(conditional)}
	       end
	    else
	       if Statement.2.2 == nil then
		  {PushStack Statement.2.1 Environment}
	       else
		  {PushStack Statement.2 Environment}
	       end
	       {SemanticStackAux}
	       {PushStack Statement.1 Environment}
	       {SemanticStackAux} 
	    end
	 end
      end
      Env = {NewCell nil}
      {PushStack AST Env}
      {SemanticStackAux}
   end
end

{SemanticStack [var ident(x) [var ident(y) [var ident(x) [nop]]]]}
declare
A = @Stack.1.2.1

{Browse @A}