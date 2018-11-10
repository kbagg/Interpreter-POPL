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
fun {CreateNewVariables Environment ListVar}
   %{Browse ["ListVar" ListVar]}
   case ListVar
   of nil then Environment
   [] ident(X)|ListX then
      local Var in
	 Var = {NewVar}
	 {AddToSAS Var}
	 {CreateNewVariables {Adjoin Environment env(X:Var)} ListX}
      end
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
	       [] literal(_) then {Exception.'raise' incompatibleTypes(ident(X) boolean)}
	       [] record|Tail then {Exception.'raise' incompatibleTypes(ident(X) boolean)}
	       else {Exception.'raise' variableUnbound(ident(X))}
	       end
	       {SemanticStackAux}
	    [] [match ident(X) P1 S1 S2] then
	       local XL XV PL PV in
		  record|PL|PV = P1
		  case {RetrieveFromSAS Environment.X}
		  of record|XL|XV then
		     local Env in
			%{Browse ["PV.1" PV.1]}
			if XL == PL andthen {IsAritySame XV.1 PV.1} then
			   Env = {CreateNewVariables Environment {List.map PV.1 fun {$ X} X.2.1 end}}
			   {Unify P1 record|XL|XV Env}
			   {PushStack S1 Env}
			else
			   {PushStack S2 Environment}
			end
		     end 
		  else
		     if {RetrieveFromSAS Environment.X} == equivalence(Environment.X) then
			{Exception.'raise' variableUnbound(ident(X))}
		     else
			{PushStack S2 Environment}
		     end
		  end
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

% {SemanticStack [var ident(x)
% 		[var ident(y)
% 		  [conditional ident(x)
% 		   [bind ident(y) literal(2)]
% 		   [bind ident(y) literal(3)]
% 		  ]
% 		]
% 	       ]
% }

% {SemanticStack [var ident(x)
% 		[var ident(y)
% 		 [var ident(v)
% 		  [
% 		   [bind ident(x)
% 		    [record literal(a)
% 		     [
% 		      [literal(b) literal(2)]
% 		      [literal(c) ident(y)]
% 		     ]
% 		    ]
% 		   ]
% 		   [match ident(x) [record literal(a)
% 				    [		     
% 				     [literal(b) ident(z)]
% 				     [literal(c) ident(w)]
% 				    ]
% 				   ]
% 		    [bind ident(v) literal(4)]
% 		    [bind ident(v) literal(5)]
% 		   ]
% 		  ]
% 		 ]
% 		]
% 	       ]
% }

%{SemanticStack [var ident(x) [var ident(y) [[var ident(x) [bind ident(x) literal(2)]] [bind ident(x) literal(3)]]]]}

%{SemanticStack [var ident(x) [nop]]}
