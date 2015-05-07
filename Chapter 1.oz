%CTMCP CHAPTER 1.9 Higher-order programming
declare fun {ShiftRight L} 0|L end

declare fun {ShiftLeft L}
   case L of H|T then
      H|{ShiftLeft T}
   else [0] end
end

declare fun {OpList Op L1 L2}
   case L1 of H1|T1 then
      case L2 of H2|T2 then
	 {Op H1 H2} | {OpList Op T1 T2}
      end
   else nil end 
end


declare fun {GenericPascal Op N}
   if N == 1 then [1]
   else L in
      L = {GenericPascal Op N-1}
      {OpList Op {ShiftLeft L} {ShiftRight L}}
   end
end

declare fun {Add X Y} X+Y end

declare fun {Xor X Y} if X == Y then 0 else 1 end end

{Browse {GenericPascal Add 10}}
{Browse {GenericPascal Xor 10}}

%CTMCP CHAPTER 1.11 Dataflow

declare X in
thread {Delay 10000} X=99 end
{Browse start} {Browse X*X}

%CTMCP CHAPTER 1.12 Explicit state

declare
C={NewCell 0}
fun {FastPascal N}
   C:=C+1
   {GenericPascal Add N}
end


declare
local C in
   C={NewCell 0}

   fun {Bump}
      C:=@C+1
      @C
   end

   fun {Read}
      @C
   end

end

{Browse {Bump}}
{Browse {Bump}}
{Browse {Read}}

%CTMCP CHAPTER 1.14 Classes

declare
fun {NewCounter}
   C Bump Read in
   C={NewCell 0}
   fun{Bump}
      C:=@C+1
      @C
   end
   fun{Read}
      @C
   end
   counter(bump:Bump read:Read)
end

%============ CTMCP: CHAPTER 1 EXCERCISES ===============

%Ex.2(a)
declare
fun {Fact N}
   if N == 1 then N
   else N*{Fact N-1}
   end
end

declare
fun {Product N K}
   if N == K then N
   else N * {Product N-1 K}
   end
end

declare
fun {Comb N K}
   if K == 0 then 1
   else {Product N (N-K+1)} div {Fact K}
   end
end

%Ex.5 Lazy evaluation
declare
fun lazy {Ints N}
   N|{Ints N+1}
end

declare
fun {SumList L}
   case L of X|L1 then X + {SumList L1}
   else 0 end
end

%this will recurse forever since Ints is infinitively recursive
%{Browse {SumList {Ints 0}}}

%Ex.6a

%Mul won't work because of
%Row 1: [1]
%Row 2: {Mul [0 1] [1 0]} => we 're multiplying by a zero each time
declare fun {Mul X Y} X * Y end

declare fun {Mul1 X Y} (X+1) * (Y+1) end

{Browse {GenericPascal Mul1 10}}

%Ex.6b Higher-order programming
declare fun {Sub X Y} X - Y end

for I in 1..10 do
   {Browse {GenericPascal Sub I}}
end

for I in 1..10 do
   {Browse {GenericPascal Mul1 I}}
end

%Ex.7 Explicit state
local X in
   X = 23
   local X in
      X = 44
   end
   {Browse X}
end

local X in
   X={NewCell 23}
   X:=44
   {Browse @X}
end

%Ex.8 Explicit state and functions

declare
local Agg in
   Agg = {NewCell 0}
   fun {Acumulate N}
      Agg:=@Agg + N
      @Agg
   end
end

{Browse {Acumulate 5}}
{Browse {Acumulate 100}}
{Browse {Acumulate 45}}

%Ex.9 Memory store
declare
local S in
   S = {NewStore}

fun {FasterPascal Op N}
   if N == 1 then
      if {Size S} == 0 then
	 {Put S N [1]}
	 {Browse ['Put' N]}
      end
      {Get S N}
   else L R in
      L = {FasterPascal Op N-1}
      R = {OpList Op {ShiftLeft L} {ShiftRight L}}
      if {Size S} < N then
	 {Put S N R}
	 {Browse ['Put' N ]}
      end
      {Get S N}
   end
end
end

for I in 1..10 do
   {Browse {FasterPascal Add I}}
end

%============ CTMCP: CHAPTER 2 EXCERCISES ===============
% Ex.5


declare Test
proc {Test X}
   case X
   of a|Z then {Browse 'case'(1)}
   [] f(a) then {Browse 'case'(2)}
   [] Y|Z andthen Y==Z then {Browse 'case'(3)}
   [] Y|Z then {Browse 'case'(4)}
   [] f(Y) then {Browse 'case'(5)}
   else {Browse X } end
end


{Test [b c a]} % => 4
{Test f(b(3))} % => 5
{Test f(a)} % => 2
{Test f(a(3))} % => 5
{Test f(d)} % => 5
{Test [a b c]} % => 1
{Test [c a b]} % => 4
{Test a|a} % => 1
{Test '|'(a b c)} % => 6

%Ex.6
declare Test
proc {Test X}
   case X of f(a Y c) then {Browse 'case'(1)}
   else {Browse 'case'(2)}
   end
end

declare X Y {Test f(X b Y)} % blocks since X and Y are not bound
declare X Y {Test f(a Y d)} % => case 2
declare X Y {Test f(X Y d)} % blocks but is clearly case 2

declare X Y
if f(X Y d)==f(a Y c) then {Browse 'case'(1)}
else {Browse 'case'(2)}
end

%Ex.7

declare Max3 Max5
proc {SpecialMax Value ?SMax}
   fun{SMax X}
      if X>Value then X else Value end
   end
end

{SpecialMax 3 Max3}
{SpecialMax 5 Max5}

{Browse [{Max3 4} {Max5 4}]} % => [4 5]

%Ex. 8
declare AndThen
fun {AndThen BP1 BP2}
   if {BP1} then {BP2} else false end
end

declare X Y in
fun {X} {Browse 'true'} true end
fun {Y} {Browse 'false'} false end

{Browse {AndThen X X}} % true eval. BP1 & BP2
{Browse {AndThen X Y}} % false eval. BP1 & BP2
{Browse {AndThen Y X}} % false eval. BP1
{Browse {AndThen Y Y}} % false eval BP1

declare OrElse
fun {OrElse X Y}
   if {X} then true
   elseif {Y} then true
   else false end
end

{Browse {OrElse X X}} % true eval. BP1
{Browse {OrElse X Y}} % true eval. BP1
{Browse {OrElse Y X}} % true eval. BP1 & BP2
{Browse {OrElse Y Y}} % false eval BP1 & BP2

%Ex.9

declare Sum1
fun {Sum1 N}
   if N==0 then 0 else N+{Sum1 N-1} end
end

declare Sum2
fun {Sum2 N S}
   if N==0 then S else {Sum2 N-1 N+S} end
end

{Browse {Sum1 100000000}} % this performs with O(1) memory
{Browse {Sum2 100000000 0}} % this performs with O(n) memory

