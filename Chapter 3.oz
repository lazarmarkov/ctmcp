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

% 3.4.5 Queues


% returns the last element in X and the rest of the list in L1
% however this implementation is slow, since ButLast depends on the list size
% i.e. it has O(n) time complexity
declare
fun {ButLast L ?X ?L1}
   case L
   of [Y] then X = Y L1 = nil
   [] Y|L2 then L3 in
      L1 = Y|L3
      {ButLast L2 X L3}
   end
end

%Amortizedd contant-time ephemeral queue

declare
fun {NewQueue} q(nil nil) end

declare
fun {Check Q}
   case Q of q(nil R) then q({Reverse R} nil) else Q end
end

declare
fun {Insert Q X}
   case Q of q(F T) then {Check q(F X|T)} end
end

declare
fun {Delete Q X}
   case Q of q(F R) then F1 in F = X|F1 {Check q(F1 R)} end
end


declare X Y Z Z2 Z3 
X={NewQueue}
Y={Insert X 1} % => [[1] nil]
Z={Insert Y 2} % => [[1] [2]]
Z2={Insert Z 3} % => [[1] [3 2]]
Z3={Delete Z2 _} % => pops [1] and reverses [3 2] => [[2 3] nil]. That's why this is an amortized implementation.
{Browse Z3} 


%Worst case constant time ephemeral queue

declare
fun {NewQueue} X in q(0 X X) end

declare
fun {Insert Q X}
   case Q of q(N S E) then E1 in E=X|E1 q(N+1 S E1) end
end

declare
fun {Delete Q X}
   case Q of q(N S E) then S1 in S=X|S1 q(N-1 S1 E) end
end

declare
fun {IsEmpty Q}
   case Q of q(N S E) then Q==0 end
end

declare X Y Z Z2 Z3 Z4
X={NewQueue} % => q(0 X X)
Y={Insert X 1} % => q(1 1|X X)
Z={Insert Y 2} % => q(2 1|2|X X)
Z2={Insert Z 3} % => q(3 1|2|3|X X)

%Example use
declare Q1 Q2 Q3 Q4 Q5 Q6 Q7 in
Q1={NewQueue}
Q2={Insert Q1 peter}
Q3={Insert Q2 paul}
local X in Q4={Delete Q3 X} {Browse X} end
Q5={Insert Q4 marty}
local X in Q6={Delete Q5 X} {Browse X} end
local X in Q7={Delete Q6 X} {Browse X} end

% example with two versions
% tip: use with the amortized queue function definitions
declare Q1 Q2 Q3 Q4 Q5 Q6 in
Q1={NewQueue}
Q2={Insert Q1 peter}
Q3={Insert Q2 paul}
Q4={Insert Q2 mary}
local X in Q5={Delete Q3 X} {Browse X} end
local X in Q6={Delete Q4 X} {Browse X} end

% Persistent queue
declare
proc {ForkD D ?E ?F}
   D1#nil=D
   E0#E1=E {Append D1 E0 E1}
   F0#F1=F {Append D1 F0 F1}
   in skip
end

declare
proc {ForkQ Q ?Q1 ?Q2}
   q(N S E)=Q
   q(N S1 E1)=Q1
   q(N S2 E2)=Q2
in
   {ForkD S#E S1#E1 S2#E2}
end

% 3.4 Trees