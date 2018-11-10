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
fun {AllVariables Statement}
   nil
end

declare
fun {FreeVariables Statement ArgList}
   local AllVar in
      AllVar = {AllVariables Statement}
      {DifferenceList AllVar ArgList}
   end
end

declare
fun {ReduceEnv Environment VarList ResEnv}
   case VarList
   of nil then ResEnv
   [] Var|VarList1 then
      local X in
	 Var = ident(X)
	 {ReduceEnv Environment VarList1 {Adjoin ResEnv env(X:Environment.X)}}
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
proc {HandleConditional X S1 S2 Environment}
   case {Dictionary.get SAS Environment.X}
   of literal(true) then {PushStack S1 Environment}
   [] literal(false) then {PushStack S2 Environment}
   [] literal(_) then {Exception.'raise' incompatibleTypes(ident(X) boolean)}
   [] record|Tail then {Exception.'raise' incompatibleTypes(ident(X) boolean)}
   else {Exception.'raise' variableUnbound(ident(X))}
   end
end

declare
proc {HandleCase X P1 S1 S2 Environment}
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
end

proc {CheckStack}
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
	 {CheckStack}
      [] [var ident(X) S] then
	 local Var in
	    Var = {NewVar}
	    {AddToSAS Var}
	    {PushStack S {Adjoin Environment env(X:Var)}}
	    {CheckStack}
	 end
      [] [bind ident(X) ident(Y)] then
	 {Unify ident(X) ident(Y) Environment}
	 {CheckStack}
      [] [bind ident(X) V] then
	 case V
	 of proce|ArgList|S then
	       local FreeVar FreeEnv in
		  FreeVar = {FreeVariables S.1 ArgList}
		  FreeEnv = {ReduceEnv Environment FreeVar nil}
		  {Unify ident(X) {Append V [FreeEnv]} Environment}
	       end
	 else {Unify ident(X) V Environment}
	 end
	 {CheckStack}
      [] [conditional ident(X) S1 S2] then
	 {HandleConditional X S1 S2 Environment}
	 {CheckStack}
      [] [match ident(X) P1 S1 S2] then
	 {HandleCase X P1 S1 S2 Environment}
	 {CheckStack}
      [] apply|ident(F)|ArgList1 then
	 local ArgList2 S FreeEnv ManageArg in
	    proce|ArgList2|S|FreeEnv = {RetrieveFromSAS Environment.F}
	    if {List.length ArgList1} == {List.length ArgList2} then
	       fun {ManageArg List1 List2 ResEnv}
		  case List2
		  of nil then ResEnv
		  [] ident(X)|L2 then
		     local Y in
			List1.1 = ident(Y)
			{ManageArg List1.2 L2 {Adjoin ResEnv env(X:Environment.Y)}}
		     end
		  end
	       end
	       {PushStack S {Adjoin {ManageArg ArgList1 ArgList2 nil} FreeEnv.1}}
	       {CheckStack}
	    else {Exception.'raise' invalidArityToProcedure(ident(F))}
	    end
	 end
      else
	 if Statement.2.2 == nil then
	    {PushStack Statement.2.1 Environment}
	 else
	    {PushStack Statement.2 Environment}
	 end
	 {PushStack Statement.1 Environment}
	 {CheckStack}
      end
   end
end

declare
proc {SemanticStack AST}      
   {PushStack AST nil}
   {CheckStack}
end

% {SemanticStack [var ident(x)
% 		[var ident(y)
% 		 [
% 		  [bind ident(x) literal(true)]
% 		  [conditional ident(x)
% 		   [bind ident(y) literal(2)]
% 		   [bind ident(y) literal(3)]
% 		  ]
% 		 ]
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
