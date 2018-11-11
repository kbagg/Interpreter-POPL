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

% {Browse {AllVariables
% 	 [bind ident(x) [proce [ident(y) ident(z)]
% 			 [bind ident(w) ident(y)]
% 			]
% 	 ]
% 	 nil}
% }

declare
fun {FreeVariables Statement ArgList}
   %{Browse ["Statement" Statement]}
   %{Browse ["ArgList" ArgList]}
   local AllVar AllVariables VarFromVal in
      fun {VarFromVal V}
	 %{Browse V}
	 case V
	 of record|Label|KeyValue then {Filter {Map KeyValue.1 fun {$ X} X.2.1 end} fun {$ X} case X of ident(Y) then true else false end end}
	 [] proce|ArgList|S then {FreeVariables S.1 ArgList}
	 else nil
	 end
      end
      fun {AllVariables Statement ResVar}
	 case Statement
	 of [var ident(X) S] then {AllVariables S ResVar}
	 [] [bind ident(X) ident(Y)] then {MergeList ResVar [ident(X) ident(Y)]}
	 [] [bind ident(X) V] then {MergeList ResVar ident(X)|{VarFromVal V}}
	 [] [conditional ident(X) S1 S2] then
	    local Var1 in
	       Var1 = {AllVariables S1 {MergeList ResVar [ident(X)]}}
	       {AllVariables S2 Var1}
	    end
	 [] [match ident(X) P1 S1 S2] then
	    local Var1 in
	       Var1 = {AllVariables S1 {MergeList ResVar [ident(X)]}}
	       {AllVariables S2 Var1}
	    end
	 [] apply|ident(F)|ArgList1 then {MergeList ResVar {MergeList ident(F) ArgList1}}
	 [] S1|S2 then
	    local Var1 in
	       Var1 = {AllVariables S1 ResVar}
	       {AllVariables S2.1 Var1}
	    end
	 else ResVar
	 end
      end
      AllVar = {AllVariables Statement nil}
      {DifferenceList AllVar ArgList}
   end
end

%{Browse {FreeVariables [bind ident(w) [proce [ident(v) ident(u)] [bind ident(v) ident(a)]]] [ident(x) ident(y)]}}

% {Browse {FreeVariables [
% 			[bind ident(x)
% 			 [record literal(a)
% 			  [
% 			   [literal(b) literal(2)]
% 			   [literal(c) ident(y)]
% 			  ]
% 			 ]
% 			]
% 			[match ident(x) [record literal(a)
% 					 [		     
% 					  [literal(b) ident(z)]
% 					  [literal(c) ident(w)]
% 					 ]
% 					]
% 			 [bind ident(v) literal(4)]
% 			 [bind ident(v) literal(5)]
% 			]
% 		       ] nil}}

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
      %{Browse ''}
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
	    if {RetrieveFromSAS Environment.X} == equivalence(Environment.X) then
	       local FreeVar FreeEnv in
		  FreeVar = {FreeVariables S.1 ArgList}
		  FreeEnv = {ReduceEnv Environment FreeVar nil}
		  {BindValueToKeyInSAS Environment.X {Append V [FreeEnv]}}
	          %{Unify ident(X) {Append V [FreeEnv]} Environment}
	       end
	    else {Exception.'raise' cantBindToProcedure(ident(X) already bound)}
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
      [] [sum ident(X) ident(Y) ident(Z)] then
	 local A B in
	    A = {RetrieveFromSAS Environment.X}
	    B = {RetrieveFromSAS Environment.Y}
	    case A#B
	    of literal(P)#literal(Q) then {PushStack [bind ident(Z) literal(P+Q)] Environment}
	    else
	       {Exception.'raise' incompatibleTypes(ident(X) ident(Y))}
	    end
	 end
	 {CheckStack}
      [] [product ident(X) ident(Y) ident(Z)] then
	 local A B in
	    A = {RetrieveFromSAS Environment.X}
	    B = {RetrieveFromSAS Environment.Y}
	    case A#B
	    of literal(P)#literal(Q) then {PushStack [bind ident(Z) literal(P*Q)] Environment}
	    else
	       {Exception.'raise' incompatibleTypes(ident(X) ident(Y))}
	    end
	 end
	 {CheckStack}
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

% {SemanticStack [var ident(w)
% 		[var ident(a)
% 		 [var ident(b)
% 		  [
% 		   [bind ident(w) [proce [ident(x) ident(y)]
% 				   [match ident(x) [record literal(a)
% 						    [		     
% 						     [literal(b) ident(z)]
% 						     [literal(c) ident(w)]
% 						    ]
% 						   ]
% 				    [bind ident(y) literal(4)]
% 				    [bind ident(y) literal(5)]
% 				   ]
% 				  ]
% 		   ]
% 		   [
% 		    [bind ident(a)
% 		     [record literal(a)
% 		      [
% 		       [literal(b) literal(2)]
% 		       [literal(c) ident(b)]
% 		      ]
% 		     ]
% 		    ]
% 		    [apply ident(w) ident(a) ident(b)] 
% 		   ]
% 		  ]
% 		 ]
% 		]
% 	       ]
% }

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

% {SemanticStack [var ident(x)
% 		[var ident(y)
% 		 [var ident(z)
% 		  [var ident(w)
% 		   [
% 		    [bind ident(x) [proce [ident(a) ident(b) ident(c)]
% 				    [product ident(a) ident(b) ident(c)]
% 				   ]
% 		    ]
% 		    [bind ident(y) literal(3)]
% 		    [bind ident(z) literal(4)]
% 		    [apply ident(x) ident(y) ident(z) ident(w)]
% 		   ]
% 		  ]
% 		 ]
% 		]
% 	       ]
% }