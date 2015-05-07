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

