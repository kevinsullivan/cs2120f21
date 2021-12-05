import data.set
import tactic.ring -- needed for later problems
namespace relation

-- Alexander Sosnkowski

/-

homework advice from lecture, ignore
x = k1 n
y = k2 x
rw to y = k1 (k2 x)

x = k1 k2 x <- will get here so both k1 and k2 need to be 1, trick to get x = y
at this point just say by basic algebra assume k1 and k2 are 1. 
do this
have foo : k1 = 1 := sorry,

on the last example of the hw, always be open to the idea of it being not true
we may need to add the assumption of an inhabited domain
would adding that make it solvable? Get credit if you say it is not true, give breif explanantion
or counter exmple
-/

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
/-
English proof: To begin the proof it is adventageous to look at the formal defenitions for 
asymmetric and not reflexive. If a binary relation is asymmetric then we know
that for every pair of β values if x is related to y, than y is not related to x.
Similarly, not reflexive means that if we assume we have some b of type β(inhabitted) and
asymmetry. We then show not reflexive by assuming reflexivity and then showing a contradiction follows.
In this particular case, if we assume reflexivity for x is related to x we can obtain a proof
that x is related to x. We can use this proof to obtain a proof that x is not related to x
by way of our asymmetric property as r x x → ¬ r x x. This is a clear contradiction.

QED

-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume b rxyyx rxx,
  cases b with B t,
  have f1 := rxx B,
  have f2 := rxyyx (f1),
  contradiction,
end

/-
It is not possible to solve this if β is not inhabited. This is because generlizations
are true on the empty set. If I have an empty trashcan than all balls within
the trash can are made of gold - this would be a tree statment on the empty set.
-/



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive,
  unfold reflexive,
  unfold asymmetric,
  assume rxyz rxx rxyyx,
  --here is where I get stuck. I must add a inhabited set otherwise the proof can not be completed
  have b : β := sorry, -- this could be added to the defenition above aswell by saying (∃(b : β), true) → ......
  have f1 := rxx b,
  have f2 := rxyyx f1,
  contradiction, 
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  unfold powerset,
  assume s1 s2 s3 s2b s3b s2s3 s3s2,
  apply set.ext,
  assume x,
  apply iff.intro _ _,
  --forward 
  assume xs2,
  apply s2s3 xs2,

  --backward
  assume xs3,
  apply s3s2 xs3,
end

/-
Informal English Proof: If we have two sets, s1 and s2, and we know that each is
a subset of the other - than it is simple to prove s1 is equivelent to s2. 
To show set equivelence we show that every element of the firt set is in the second,
and vice versa. The defenition of subset is that, in order for the first set 
to be a subset of the second, every element of the subset must be a member of the second.
This is remarkably similar to how we define set equivelence (really the same thing but in one direction)
Thus, we prove each side of our if and only if in this manner and arive at a proof for s1 = s2.
QED 
-/

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/
-- by the precious ring axioms
-- A: For any n, 1 divides n.

example : ∀ n, divides 1 n :=
begin
  unfold divides,
  assume n,
  apply exists.intro n, -- putting an underscore bricks code
  ring, -- do not use ring with underscores
end

/-
Informal English Proof: 1 will divide any natural number. To prove this we 
show (by our defenition of divides) that for any n we can find a witness k
such that n = 1  * k. For our proof we say k is n simplifying our proof to a proof of
k = 1 * k which by basic algebra is true. 
QED
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  unfold divides,
  assume n,
  apply exists.intro 1,
  ring,
end

/-
Informal English Proof: Any natural number will divide itself. The logic to prove
this is an inverse (but similar) to the logic used for the prior problem. Like before
we redefine our problem by looking at our defenitions to n = n * k. The witness we use 
here for k is 1 instead of n. This leaves us needing to prove once again n = n * 1 
which is accomplished through basic logic - the precious ring axioms!
QED
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 

/-
Informal English Proof: The proof is identical / logially equivelent to the prior problem.
We show any natural number can divide itself by our defenition of reflexive.

-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z ykx zky,
  cases ykx with k1 ynx,
  cases zky with k2 zny,
  apply exists.intro (k1 * k2),
  rw zny,
  rw ynx,
  ring,
end 

/-
Informal English Proof: We can show that divides is transitive on the natural numbers by showing that if
x divides y and y divides z then x divides z by looking towards our defenitions. we must prove z = x * k
Since y = x * k1 and z = y * k2, we can use basic subsitution rules to rewrite z = (x * k1) * k2
and through basic algebra we see z = x * (k1 * k2) where k1 * k2 is just some other constant.
thus x divides z QED
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here: No, if 5 divides 30, 30 does not divide 5 in the natural numbers.
-- this would only be true for number sets containing fractional values. 
-- 5 * 6 = 30
-- 30 * 1/6 = 5 
-- but, 1/6 is not a natural number 


/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y ykx xky,
  cases ykx with k1 ykx,
  cases xky with k2 xky,
  rw ykx,
  have k11 : k1 = 1 := sorry, -- these assumptions are allowed I believe
  have k21 : k2 = 1 := sorry,
  rw k11,
  ring,
end

/-
We can show that divides is anti_symmetric by showing that x divides y implies y divides x only when x = y.
If we know x divides y and y divides x (i.e y = k * x and x = k * y)
then it can be shown through subsitution that x = y is rewrittable as x = k * x
by assuming k = 1 and through some basic algebra we can show x = x which by the reflexive property
of equality is true and thus QED
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume rxyyx x rxx,
  have f := rxyyx rxx,
  contradiction,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume notrxx rxyyzxz x y rxy ryx,
  have rxx := rxyyzxz rxy ryx,
  have contra := notrxx x,
  contradiction,
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume rxyyzxz notrxyyx notrxx,
  --here is where I begin to run into issues so I assume it is inhabbited and a relation exists
  /- this is an example where it would work / be true but it is not true for all cases!
  have x : β := sorry,
  have y : β := sorry,
  have rxy : r x y := sorry,
  have ryx : r y x := sorry,
  --have rxx : r x x := sorry,
  have f1 := notrxx x,
  have f2 := rxyyzxz rxy ryx,
  contradiction,
  -/
end
/-
Informal English Proof: If something is transitive and not symmetric, then
we can not definetly say it is no irreflexive (i.e there exists some reflexive relation).

imagine 
objects a and b
The map 

{

r a a
r a b

}

This is transitive, not symmetric as r b a is not true, and still reflexive as r a a.


( a )-----> ( a ) ------> ( b )


-/

end relation
