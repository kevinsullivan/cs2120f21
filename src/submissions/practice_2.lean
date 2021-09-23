/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro -- true has the proof that it is true through true.intro. This is axiomatic and not complex.

example : false := -- I cannot answer this with a proof, it does not exist. trick question? why? It is a type which has no values, uninhabbited. 
-- to be false is to have no proofs
/-
As for all proofs involving if and only ifs, this must be split into two implications ussing iff.intro
one is P ∨ P → P and the other is P → p ∨ p. These are each individually proved 
first in the forward direction (reading the iff left to right) and then backwards direction (reading the iff right to lef)
The forward direction is completed by splitting the or with or.elim to check if both the left and right side of the or imply p.
The backwards direction is completed through the use of the or introduction rule
which allows p to be extended as p ∨ (some other prop) in this case p ∨ p

-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
    assume porp,
    apply or.elim porp,
    -- left disjunct 
      assume p,
      exact p,
    -- right disjunct 
        assume p2,
        exact p2,
  --backwords
      assume P2,
      exact or.intro_right P P2,
end

#check @or.intro_left
/-
This proof began similarly to the one above. Iff.intro allows us to prove both sides of the implication one at a time. 
The forwards direction is solved by assuming the first half of the implication (the intro rule for an implication)
and then eliminating one side of the and using the left and elimination rule. This leaves us with a proof of p which can be applied
The backwards direction is completed by assuming p (intro rule for implications once again)
and then using the and introduction rule to construct a proof of p ∧ p from just p.

-/
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
    assume por,
    apply and.elim_left por,
  --backwords 
    assume por2,
    apply and.intro por2 por2,
end
/-
The proof below was begun by assuming basic propositions P and Q
Next, the introduction rule for if and only if was applied and each implication was solved individually
the forward direction was solved by assuming the first half of the implication and then applying symetry to show a proof for the second half
This same method was applied in the backwards direction to finish the proof as both directions where proven true.
-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  --forwards
    assume z,
    apply or.symm z,
  --backwords
    assume z2,
    apply or.symm z2,
end

/-
The proof below was solved in a similar manner as to the one above
Basic assumptions of propositions P and Q were made.
The introduction rule was applied to if and only and both resulting implications where proven
For each direction the first half of the implication was assumed (by way of implication introduction rule)
and then by property of symetry of and rearagned to give the respectively needed proof.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume Q,
  assume P,
  apply iff.intro _ _,
  --forwards
    assume z,
    apply and.symm z, 
  --backwards
    assume z2,
    apply and.symm z2, 
end
/-
Basic assumptions of propostitions p, q, and r were made
the introduction rule of if and only if was applied to split the proof into two implication proofs
The forward direction was shown true by first using and elimnation rules to seperate proofs for p and a proof for q ∨ r
Then, the elimination rule for or was used to show that for either r ∨ q being true 
they could be combined with the above proof of p using the and.intro rule to gain a proof for (p ∧ q) ∨ (p ∧ r)
The backwards direction was proven by assuming the first half of the implication (p ∧ q) ∨ (p ∧ r)
and splitting the implication into two seperate implications using the or elimination rule. (effectiely prove both sides of the or imply p ∧ (q ∨ r))
Showing a proof for p ∧ (q ∨ r) for both sides was done individually using the and introduction rule combined with the or introduction rule where the left or right side would be choosen as the situation needed. 
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume p,
  assume q,
  assume r,
  apply iff.intro _ _,
  --forwards
    assume z,
    have a1 : p := and.elim_left z,
    have a2 : q ∨ r := and.elim_right z,
    apply or.elim a2,
    --forwards
      assume q,
      apply or.intro_left _ _,
      apply and.intro a1 q,
    --backwards 
      assume r,
      apply or.intro_right _ _,
      apply and.intro a1 r,

  --backwards
      assume y,
      apply or.elim y,
      --forwards
        assume x,
        have a3 : p := and.elim_left x,
        have a4 : q := and.elim_right x,
        apply and.intro a3 (or.intro_left _ _),
        apply a4,
      --backwords 
        assume v,
        have a5 : p := and.elim_left v,
        have a6 : r := and.elim_right v,
        apply and.intro a5 (or.intro_right _ _),
        apply a6,
end
/-
The proof begins with basic assumptions of propositions p, q and r.
the introduction rule for if and only if is used to prove the implication from two directions (forward and back)
The forward direction was proven by assuming the first half of the implication defined as z.
z was then split into two cases using the elimination rule for or. (one case being p the other being q ∧ r)
By combinging two or introduction rules with an and introduction rule a proof can be created for (p ∨ q) ∧ (p ∨ r).
the backwards direction is proven by first assuming the left of the implication (by way of the introduction rule of implication)
and then splitting it into two different proofs, one for q and one for r. 
these are recombined using or and and introduction rules as is needed.
Finally, case analysis is used to show two possible cases, one assuming p and the other assuming q
each one of these cases is resolved by use of and introduction rules and or elimination rules when neccessary
-/
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume p,
  assume q,
  assume r,
  apply iff.intro _ _,
  --forwards
    assume z,
    apply or.elim z,
    --forwards once more
      assume y,
      apply and.intro (or.intro_left _ _) (or.intro_left _ _),
      apply y,
      apply y,
  --backwards
    assume x,
    have x1 : q := and.elim_left x,
    have x2 : r := and.elim_right x,
    apply and.intro (or.intro_right _ _) (or.intro_right _ _), 
    apply x1, 
    apply x2,
  --backwards once more
    assume c,
    have x3 : p ∨ q := and.elim_left c,
    have x4 : p ∨ r  := and.elim_right c,
    cases x3,
    --case 1
    apply or.intro_left _,
    apply x3,
    apply or.elim x4,
    assume p,
    apply or.intro_left _,
    apply p,
    --case 2
    assume r,
    apply or.intro_right _,
    exact and.intro x3 r,
end

/-
basic assumptions of propositions p and q are made.
if and onyly if is split into two implications by way of the introduction rule of if and only if
the forwards direction is solved by assuming the first half of the implication (introduction rule of implication)
and then a proof for p and a proof for p ∨ q is made by use of ands elimination rules.
With a proof for p isolated, p is already proven
The backwards direction is proven by first assuming p
then combining the or introduction rule with the and introduction rule it can be shown that with a proof of p 
it is possible to construct a proof for p ∧ (P ∨ (some blank / other proposition) )
-/
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume p q,
  apply iff.intro _ _,
  --forwards
    assume a,
    have b : p := and.elim_left a,
    have c : p ∨ q  := and.elim_right a,
    apply b, 
  --backwards   
    assume a,
    apply and.intro a (or.intro_left _ _),
    apply a,
end

/-
basic assumptions of propositions p and q are made.
the introduction rule for if and only if is used to split the proof into a proof of two implications
the forwards direction is solved by assuming the first half of the implication
and then looking at the two cases resulting from the assumption.
The first case is solved because p can simply be applied (this case assumes p is true and asks for a proof of p so no work is to be done)
the second case can be solved by applying the introduction rule of or to show p implies p ∨ (p ∧ q) - the right side of the or is irrelevant because a proof of p ∨ (anything else) can be made with just p and the or introduction rule
the backwards direction is solved by assuming p, showing p can be extended to p ∨ (something other propostion) through the 
use of the or introduction rule.
-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume p q,
  apply iff.intro _ _,
  --forwards
    assume a,
    cases a,
    apply a,
    apply and.elim_left a,
  --backwards
    assume a,
    apply or.intro_left _ _,
    apply a,

end
/-
assuming a proposition p, the introduction rule for if and only if can be used to break the proof into two implications
the forward implication is sovled by assuming p ∨ true and then simply by defenition of true or using the introduction rule of true showing p ∨ true → true 
the backwards direction is shown to be true by assuming true and by using the introduction rule of or it can be shown a proof of p can be extended to a proof of p ∨ true.
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
    assume a,
    apply true.intro,
  --backwards
    assume a,
    apply or.intro_right _ _,
    apply a,
end
/-
assuming a proposition p and by using the introduction rule for if and only if the proof can be split into two implication problems
the forward direction is solved assuming p and showing that by the introduction rule of or a proof of p ∨ false is true when p is true and therefore a proof of p is sufficent
the proof of p assumed is then applied
the backwards direction is solved by assuming p ∨ false. Then by the elimination rule for or two cases can be looked at one were false implies p and one were p implies p
P implies p is trivial (simply assume p and then apply that proof of p to show p)
The elimination rule for false can be used on the second case to show that false implies anything and thus the proof is completed.
-/
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _,
  --forward
    assume a,
    apply or.intro_left _ _,
    apply a,
    --backward
    assume a,
    apply or.elim a,
    assume b,
    apply b,
    assume f,
    apply false.elim,
    apply f, -- this last section is something I need to better understand. 
end
/-
First  some proposition p is assumed and then
 using the introduction rule of if and only if the problem is split into two seperate implications.
 the forward direction is solved by assuming p ∧ true then using ands elimination rule to isolate the proof of p
 this is then applied to show that p ∧ true → p as a proof of p can be found by assuming p ∧ true
 the backwards direction is sovled by assuming p and showing that a proof of p ∧ true can be constructed
 using the and introduction rule and the introduction rule for true (this is simply a proof of true and thus we can combine a proof of p with a proof of true togethar with ands introduction rule)

-/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward 
    assume a,
    have p : P := and.elim_left a,
    apply p,
  --backward 
    assume a,
    apply and.intro a _,
    apply true.intro,  
end
/-
A propositon p is assumed. The poblem is split into two seperate implications through the use of if and only ifs introduction rule.
the forward direction is solved by assuming p ∧ false (through the introduction rule of implications we are allowed to make this assumption) 
then showing we can isolate false through the elimination rule of and. 
this lets us show false implies false by simply applying our isolated false (false has no proof which is important to note)
the backwards direction is solved by assuming false wich inherintly  implies anything through the elimination rule of false. Thus the proof is completed
-/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume a,
    have f : false := and.elim_right a,
    apply f,
  --backward
    assume a,
    apply false.elim,
    apply a,
end
-- QED