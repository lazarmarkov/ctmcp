%===============CHAPTER 3=================

%3.2.3 Using local procedures

% Square root using Newton's guess method
% the helper functions: Improve, GoodEnough and SqrtIter
% are recreated on each call to Sqrt
% this is a good balance between readability and performance
% the two extremes would be to:
% 1. create the helpers outside Sqrt, requiring additional argument,
%    namely, Guess. This reduces readability
% 2. create the helpers inside the functions that need them.
%     This would mean Improve and GoodEnough are declared within SqrtIter
%     This would mean the helper functions are recreated with each call
%     to SqrtIter which is bad for performance
declare
fun {Sqrt X}
   fun {Improve Guess}
      (Guess + X/Guess) / 2.0
   end
   fun {GoodEnough Guess}
      {Abs X-Guess*Guess}/X < 0.00001
   end
   fun {SqrtIter Guess}
      if {GoodEnough Guess} then Guess
      else {SqrtIter {Improve Guess}}
      end      
   end
   Guess=1.0
in
   {SqrtIter Guess}
end

{Browse {Sqrt 2.0}}

%3.4.2.1 Thinking recursively

% Naive list length func
% This executes with a stack size of O(listLength)
% because the last operation is addition and not a recursive call
% therefore a last call optimization cannot be applied by the compiler
declare
fun {Length Ls}
   case Ls
   of nil then 0
   [] _|Lr then 1+{Length Lr}
   end
end

%3.4.2.2 Recursive functions and their domains

% Nth element function
declare
fun {Nth Xs N}
   if N==1 then Xs.1
   elseif N>1 then {Nth Xs.2 N-1}
   end
end
local X = [a b c d]
in   
   {Browse {Nth X 3}} % => "c"
%   {Browse {Nth X 5}} % => error, 5 is outside the list
%   {Browse {Nth X ~1}} % => error, the if else stmt has no case for negative integers
end

%3.4.2.4 Converting recursive to iterative computations

% iterative implementation of Length
% this performs in a constant stack size
% because of last call optimization
declare
fun {IterLength I Ys}
   case Ys
   of nil then I
   [] _|Yr then {IterLength I+1 Yr}
   end
end

{Browse {IterLength 0 [a b c]}} % => 3

%3.4.2.6 Constructing programs by following the type

% LengthL follows the definition of the list type
% (NestedList T) ::= nil
%                    | (NestedList T) '|' (NestedList T)
%                    | T '|' (NestedList T)
declare
fun {LengthL Xs}
   case Xs
   of nil then 0
   [] X|Xr andthen {IsList X} then
      {LengthL X} + {LengthL Xr}
   [] X|Xr then
      1+{LengthL Xr}
   end
end

declare
X = [ [1 5] 4 7 [5] [5 10 11]]
Y = foo

{Browse {LengthL X}} % => 8
{Browse {LengthL Y}} % => exception, foo is not a list, this is correct

% LengthL2 follows the definition of the list type
% (NestedList2 T) ::= nil
%                    | (NestedList2 T) '|' (NestedList2 T)
%                    | T 
declare
fun {LengthL2 Xs}
   case Xs
   of nil then 0
   [] X|Xr  then
      {LengthL2 X} + {LengthL2 Xr}
   else 1 end
end

{Browse {LengthL2 X}} % => 8
{Browse {LengthL2 Y}} % => 1, which is incorrect, since Y is not a list


% 3.4.2.7 Sorting with mergesort
declare
fun {Merge Xs Ys}
   case Xs#Ys
   of nil#Ys then Ys
   [] Xs#nil then Xs
   [] (X|Xr) # (Y|Yr) then
      if X<Y then X|{Merge Xr Ys}
      else Y|{Merge Xs Yr}
      end
   end
end

declare
proc {Split Xs ?Ys ?Zs}
   case Xs
   of nil then Ys=nil Zs=nil
   [] [X] then Ys=[X] Zs=nil
   [] X1|X2|Xr then Yr Zr in
      Ys=X1|Yr
      Zs=X2|Zr
      {Split Xr Yr Zr}
   end
end

declare
fun {MergeSort Xs}
   case Xs
   of nil then nil
   [] [X] then [X]
   else Ys Zs in
      {Split Xs Ys Zs}
      {Merge {MergeSort Ys} {MergeSort Zs}}
   end
end

%3.4.3 Accumulators

%Merge sort with an accumulator


% In constrast with the previous MergeSort,
% this uses splits the list into halves,
% where the previous split the odd-numbered list elements from the even
% This impl consumes less memory since it doesn't create two split lists
% They are defined defined implicitly by
% the accumulating param and the number of elements
declare
fun {MergeSort Xs}
   fun {MergeSortAcc L1 N}
      if N==0 then
	 nil # L1
      elseif N==1 then
	 [L1.1] # L1.2
      elseif N>1 then
	 NL=N div 2
	 NR=N-NL
	 Ys # L2 = {MergeSortAcc L1 NL}
	 Zs # L3 = {MergeSortAcc L2 NR}
      in
	 {Merge Ys Zs} # L3
      end
   end
in
   {MergeSortAcc Xs {Length Xs}}.1
end

% 3.4.4 Difference lists
declare
fun {AppendD D1 D2}
   S1#E1=D1
   S2#E2=D2
in
   E1=S2
   S1#E2
end

local X Y in
   {Browse {AppendD (1|2|3|X)#X (4|5|Y)#Y}}
end

% flattens a nested list
% It is inefficient, since it does many Append operations
declare
fun {Flatten Xs}
   case Xs
   of nil then nil
   [] X|Xr andthen {IsList X} then
      {Append {Flatten X} {Flatten Xr}}
   [] X|Xr then
      X|{Flatten Xr}
   end
end

declare X=[1 [2 3] 4 [5 [6]]]

{Browse {Flatten X}} % => [1 2 3 4 5 6]

% This version of flatten uses difference lists
% to con the nested lists. A cons operation on diff lists
% performs in constant time, so this is faster than the prev impl.
declare
fun {Flatten Xs}
   proc {FlattenD Xs ?Ds}
      case Xs
      of nil then Y in Ds=Y#Y
      [] X|Xr andthen {IsList X} then Y1 Y2 Y4 in
	 Ds=Y1#Y4
	 {FlattenD X Y1#Y2}
	 {FlattenD Xr Y2#Y4}
      [] X|Xr then Y1 Y2 in
	 Ds=(X|Y1)#Y2
	 {FlattenD Xr Y1#Y2}
      end
   end
   Ys
in
   {FlattenD Xs Ys#nil} Ys 
end

{Browse {Flatten X}} % => [1 2 3 4 5 6]


% same as prev, but with two arguments
% S = start E = tail of the resulting list
declare
fun {Flatten Xs}
   proc {FlattenD Xs ?S E}
      case Xs
      of nil then S=E
      [] X|Xr andthen {IsList X} then Y2 in
	 {FlattenD X S Y2}
	 {FlattenD Xr Y2 E}
      [] X|Xr then Y1 in
	 S=X|Y1
	 {FlattenD Xr Y1 E}
      end
   end
   Ys
in {FlattenD Xs Ys nil} Ys end

{Browse {Flatten X}} % => [1 2 3 4 5 6]

% further simplificaiton:
% FlattenD as a func that returns the list as a result

declare
fun {Flatten Xs}
   fun {FlattenD Xs E}
      case Xs
      of nil then E
      [] X|Xr andthen {IsList X} then
	 {FlattenD X {FlattenD Xr E}}
      [] X|Xr then
	 X|{FlattenD Xr E}
      end
   end
   in
   {FlattenD Xs nil}
end

{Browse {Flatten X}} % => [1 2 3 4 5 6]

