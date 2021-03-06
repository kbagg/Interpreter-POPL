declare SAS BindValueToKeyInSAS BindRefToKeyInSAS RetrieveFromSAS
SAS = {Dictionary.new}

declare
fun {DifferenceList L1 L2}
   case L1
   of nil then nil
   [] H|T then
      if {Member H L2} then {DifferenceList T L2}
      else H | {DifferenceList T L2}
      end
   end
end

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
   {Dictionary.put SAS Key [Key]}
end

declare
fun {RetrieveFromSAS Key}
   case {Dictionary.get SAS Key}
   of literal(X) then literal(X)
   [] record|Label|KeyValue then {Dictionary.get SAS Key}
   [] proce|ArgList|S|FreeEnv then {Dictionary.get SAS Key}
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
   %{Browse ["Val to Key" Key Val]}
   local KeyList in
      KeyList = {Dictionary.get SAS Key}
      {PutVal KeyList Val}
   end
end

declare
proc {BindRefToKeyInSAS Key1 Key2}
   %{Browse ["Key to Key" Key1 Key2]}
   local MList in
      MList = {MergeList {Dictionary.get SAS Key1} {Dictionary.get SAS Key2}}
      {PutVal MList MList}
   end
end

   
   