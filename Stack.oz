\insert 'Unify.oz'

declare Stack Count
Stack = {NewCell nil}
Count = {NewCell 1}

declare
fun {NewVar}
   local Var in
      Var = {Append "var" {Int.toString @Count}}
      Count := @Count + 1
      {VirtualString.toAtom Var}
   end
end

declare
fun {PopStack}
   case @Stack
   of nil then [nil {NewCell nil}]
   else
      local Top in
	 Top = @Stack.1
	 Stack := @Stack.2
	 Top
      end
   end
end

declare
proc {PushStack Statement Environment}
   Stack := {Append [[Statement Environment]] @Stack}
end

declare
proc {PrintStack}
   case @Stack
   of H|T then
      {Browse H}
      {Browse H.1}
      local Env in
	 Env = H.2.1
	 {Browse @Env}
      end
   else
      skip
   end
end

declare
proc {SemanticStack AST}
   local SemanticStackAux Env in
      proc {SemanticStackAux}
	 local Statement Environment in
	    {Browse 'begin case statement'}
	    [Statement Environment] = {PopStack}
	    {Browse ["Statement" Statement]}
	    {Browse ["Environment" @Environment]}
	    {Browse ["SAS" {Dictionary.entries SAS}]}
	    case Statement
	    of nil then skip
	    [] [nop] then
	       {SemanticStackAux}
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
	       {SemanticStackAux}
	    [] [bind ident(X) V] then
	       {Unify ident(X) V @Environment}
	       {Browse SAS}
	       {SemanticStackAux}
	    [] [conditional ident(X) S1 S2] then
	       case {Dictionary.get SAS @Environment.X}
	       of literal(true) then {PushStack S1 Environment}
	       [] literal(false) then {PushStack S2 Environment}
	       else {Exception.'raise' variableUnbound(conditional)}
	       end
	       {SemanticStackAux}
	    else
	       {Browse here}
	       if Statement.2.2 == nil then
		  {PushStack Statement.2.1 Environment}
	       else
		  {PushStack Statement.2 Environment}
	       end
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

{SemanticStack [var ident(x) [var ident(y) [bind ident(x) ident(y)]]]}
%{SemanticStack [var ident(x) [nop]]}

{PrintStack}