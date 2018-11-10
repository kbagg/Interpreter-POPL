declare SAS BindValueToKeyInSAS BindRefToKeyInSAS RetrieveFromSAS
SAS = {Dictionary.new}

declare
fun {MergeList L1 L2}
   case L1
   of nil then L2
   [] H|T then
      if {Member H  L2} then {MergeList T L2}
      else H | {MergeList T L2}
      end
   end
end

declare
proc {AddToSAS Key}
   {Browse Key}
   {Dictionary.put SAS Key [Key]}
   {Browse {Dictionary.entries SAS}}
end

{Browse {VirtualString.toAtom "b"}}

declare
fun {RetrieveFromSAS Key}
   case {Dictionary.get SAS Key}
   of literal(X) then literal(X)
   [] record|Label|KeyValue then {Dictionary.get SAS Key}
   else equivalence(Key)
   end
end

declare
proc {PutVal L1 K}
   case L1
   of nil then skip
   [] H|T then {Dictionary.put SAS H K} {PutVal T K}
   end
end

declare
proc {BindValueToKeyInSAS Key Val}
   local KeyList in
      KeyList = {Dictionary.get SAS Key}
      {PutVal KeyList Val}
      if {Dictionary.member SAS Val} then
	 local ValList in
	    ValList = {Dictionary.get SAS Val}
	    {Dictionary.put SAS Val {MergeList KeyList ValList}}
	 end
      else {Dictionary.put SAS Val KeyList}
      end
   end
end

declare
proc {BindRefToKeyInSAS Key1 Key2}
   local MList in
      MList = {MergeList {Dictionary.get SAS Key1} {Dictionary.get SAS Key2}}
      {PutVal MList MList}
   end
end

   
   