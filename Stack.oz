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
   of nil then [nil nil]
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
   of nil then {Browse "Stack nil"}
   else
      local Top S E in
	 Top = @Stack.1
	 [S E] = Top
	 {Browse ["Stack" S E]}
      end
   end
end
      
declare
proc {SemanticStack AST}
   local SemanticStackAux Env in
      proc {SemanticStackAux}
	 local Statement Environment in
	    [Statement Environment] = {PopStack}
	    {Browse ["Statement" Statement]}
	    {Browse ["Environment" Environment]}
	    {Browse ["SAS" {Dictionary.entries SAS}]}
	    {PrintStack}
	    {Browse ''}
	    case Statement
	    of nil then skip
	    [] [nop] then
	       {SemanticStackAux}
	    [] [var ident(X) S] then
	       local Var in
		  Var = {NewVar}
		  {AddToSAS Var}
		  {PushStack S {Adjoin Environment env(X:Var)}}
		  {SemanticStackAux}
	       end
	    [] [bind ident(X) ident(Y)] then
	       {Unify ident(X) ident(Y) Environment}
	       {SemanticStackAux}
	    [] [bind ident(X) V] then
	       {Unify ident(X) V Environment}
	       {SemanticStackAux}
	    [] [conditional ident(X) S1 S2] then
	       case {Dictionary.get SAS Environment.X}
	       of literal(true) then {PushStack S1 Environment}
	       [] literal(false) then {PushStack S2 Environment}
	       else {Exception.'raise' variableUnbound(conditional)}
	       end
	       {SemanticStackAux}
	    else
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
      {PushStack AST nil}
      {SemanticStackAux}
   end
end

{SemanticStack [var ident(x)
		[var ident(y)
		 [var ident(z)
		  [
		   [bind ident(x)
		    [record literal(a)
		     [
		      [literal(b) literal(2)]
		      [literal(c) ident(y)]
		     
		    ]
		   ]]
		   [bind ident(x)
		    [record literal(a)
		     [		     
		      [literal(b) ident(z)]
		      [literal(c) literal(3)]
		     ]
		    ]
		   ]
		  ]
		 ]
		]
	       ]		   
}

%{SemanticStack [var ident(x) [var ident(y) [[var ident(x) [bind ident(x) literal(2)]] [bind ident(x) literal(3)]]]]}

%{SemanticStack [var ident(x) [nop]]}
