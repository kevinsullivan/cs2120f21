import data.set
import tactic.ring

namespace relation

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
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume ex,
  unfold asymmetric,
  assume asym,
  apply not.intro,
  unfold reflexive,
  assume refl,
  cases ex with b pf,
  have rbb := refl b,
  have nrbb := asym rbb,
  contradiction,
end

/-
English-language proof:
Given that there is a b of type β and a proof that for all objects of type
β x and y if there exists a binary relation from x to y, then there is not a 
binary relation between y and x then it is not true that there exists a 
binary relation from an object to itself. To prove this first assume 
the existence of b and the assymetry described above. Then apply the 
introduction rule for not and assume the reflexive relation to only need 
a proof of false. From here a case analysis of the existence of b provides
a proof of true and b of type β. From this, we can produce a proof of the
binary relation r b b using the assumed rule of reflexivity and a proof of 
¬ r x x by applying the assymetry relation to r b b. This produces a 
contradiction which proves false. 


If you remove the first condition:
If b is uninhabited then the proposition isn't true because in an empty set 
there are no binary relations r x y so the conditions for assymetry are never met
and therefore no contradiction can be formed to reflexivity. 
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
example : (∃ (b: β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume ex,
  unfold transitive,
  assume trans,
  unfold reflexive,
  assume refl,
  apply not.intro,
  unfold asymmetric,
  assume asym,
  cases ex with b pf,
  have rbb := refl b,
  have nrbb := asym rbb,
  contradiction,
end

/-
Added the premise (∃ (b: β), true) in order to prove the proposition
-/




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
  assume s s1 s2,
  unfold powerset,
  assume power1,
  assume power2,
  show (∀(x:β), x ∈ s1 → x ∈ s2) → (∀ (x : β), x ∈ s2 → x ∈ s1) → s1 = s2,
  assume s1subs2,
  assume s2subs1,
  apply set.ext,
  assume x,
  apply iff.intro,
  have xin12 := s1subs2 x,
  exact xin12,
  have xin21 := s2subs1 x,
  exact xin21,
end

/-
You are given sets s s1 and s2 of type β where s1 and s2 are in the powerset of s. 
You are also given that s1 is a subset of s2 and s2 is a subset of s1. Prove that 
s1 = s2. s1 = s2 can be rewritten as ∀ (x : β), x ∈ s1 ↔ x ∈ s2. From here we can 
assume x and apply the introduction rule for iff to split the proof into two proofs
x ∈ s1 → x ∈ s2 and x ∈ s2 → x ∈ s1. 
First direction:
Using the proofs of x and that s1 is a subset of s2 we can construct a proof that 
x ∈ s1 → x ∈ s2 which is what we are trying to prove and therefore the first 
disjunct is true. 
Second direction:
Using the proofs of x and that s2 is a subset of s1 we can construct a proof that 
x ∈ s2 → x ∈ s1 which is what we are trying ot prove and therefore the second disjunct
is true. 
With both directions being true, the overall proposition is true. 
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

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end

/-
Prove that for all natural numbers n, 1 divides n. First assume n is of type 
ℕ. From here we must prove that there exists a value k such that n = k * 1. A
pplying the introduction rule we can say k is equal to n which changes our proof t
o one of n = n * 1. This is true by basic algebra. 
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-
Prove that for all natural numbers n, n divides n. First assume n is of type
ℕ. From here we must prove that there exists a k such that n = k * n. Applying 
the introduction rule of exists with the value 1 yields n = 1 * n. This is true
by basic algebra. 
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive,
  assume x,
  unfold divides,
  apply exists.intro 1,
  ring,
end 


/-
Prove that for all x of type ℕ, x divides x. First assume x is an arbitrary value
of type ℕ. Now you must prove that there exists some k such that x = k * x. From 
here you can apply the introduction rule of exists with the value 1 to yield
x = 1 * x. This is true by basic algebra. 
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive,
  assume x y z,
  unfold divides,
  assume xdivy,
  assume ydivz,
  cases xdivy with n k1,
  cases ydivz with n1 k2,
  apply exists.intro (n * n1),
  rw k2,
  rw k1,
  ring,
end 

/-
Prove that for all x, y, and z of type ℕ if x divides y and y divides z then x 
divides z. First assume x y and z of type ℕ, x divides y, and y divides z. then
apply a case analysis of x divides y and y divides z to have proofs that 
n and n1 are values of type ℕ, y = n * x, and z = n1 * y. You want to prove that 
there exists a value k such that z = k * x. Apply the introduction rule of 
exists with (n * n1) to yield z = n * n1 * x. Now we can use the proof that 
z = n1 * y to rewrite the proof to be n1 * y = n * n1 * x. Next we can use the proof
that y = n * x to rewrite the proof to be n * n1 * x = n * n1 * x. This is true by 
basic algebra. 
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
No, divides is not symmetric in the natural numbers. A counterexample is 3 and 9. 
3 divides 9 but 9 does not divide 3. This is because 9 = 3 * 3, but there is no 
natural number k that satisfies 3 = k * 9. 
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric,
  unfold divides,
  assume x y divxy divyx,
  cases divxy with n1 yx,
  cases divyx with n2 xy,
  have n2 : n2 = 1 := sorry,
  have n1 : n1 = 1 := sorry, --Only way for x = ky and y = nx to be true is for k=n=1
  rw yx,
  rw n1,
  ring,
end


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
  unfold asymmetric,
  unfold irreflexive,
  assume asym x,
  apply not.intro,
  assume rxx,
  have nrxx := asym rxx,
  contradiction,
end

/-
Assumme that a binary relation r is asymmetric, prove that that means it is 
also irreflexive. First assume that r is asymmetric which means that for all
x and y of arbitrary type β if x is related to y, y is not related to x. Next, we 
can assume that r is reflexive and prove that is false to prove that r is 
irreflexive. By the reflexive property we can assume a proof of r x x. Then, 
we can use the proof of asymmetry on the proof of r x x to create a proof of 
¬ r x x. This creates a contradiction, proving the reflexive property false and the
irreflexive property true. 
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive,
  unfold transitive,
  unfold asymmetric,
  assume irrrefl,
  assume trans,
  assume x y,
  assume rxy,
  apply not.intro,
  assume ryx,
  have nrxx := irrrefl x,
  have rxx : r x x := trans rxy ryx,
  contradiction,
end

/-
Prove that given a relation r that is irreflexive and transitive, it is
asymmetric. First assume that r is irreflexive and transitive. Then assume x and 
y are objects of an arbitrary type β. Asymmetry says that for all x and y if x 
is related to y, y is not related to x. To prove this we can assume a proof that
x is related to y and build a proof that y is not related to x to prove that
the relation is asymmetric. Through the proof of irreflexivity we can construct a 
proof of ¬ r x x. From here, if r were symmetric then the transitive property 
could be used with r x y and r y x to create a proof of r x x which direclty
contradicts the ¬ r x x from before. Therefore r must be asymmetric.  
-/

-- C
example : (∃ (x : β ), true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive,
  unfold symmetric,
  unfold irreflexive,
  assume x,
  assume trans,
  assume nsymm,
  apply not.intro,
  assume irrefl,
  cases x with x pf,
  have nrxx := irrefl x,
  /-
  This is impossinle to prove. It is possible to create a proof of ¬ r x x but no 
  way to create a contradiction to prove the overall proposition false.  
  -/
end

end relation
