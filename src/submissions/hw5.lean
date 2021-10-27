import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

What is to be shown is as follows: (1) there  is a function, f, that maps every 'a' of type α with property p to a value, f a, of type
β with property q, and (2) if there is an 'a' with property p, then it can be concluded there is some 'b' of type β with property q.

English Language Proof

It is possible to (by way of the elimination rule for exists) obtain a proof for a function f that upon recieving something of type α, 
returns something of type β. We also know that for all 'a' of type α, if property p can be proven for that a, we have sufficently shown
a proof for property q of the f mapped β value (i.e f a). Thus, if their exists some 'a' of type α with property p (which is assumed
by the introduction rule of implies), we can obtain some β through function f and know that since their exists some 'a' with property p, 
their must exist some 'b' of type β (i.e f a) that has property q. 

-/


-- Give your formal proof here
begin
  intros a b,
  cases a,
  cases b,
  apply exists.intro (a_w b_w) _,
  have q := a_h b_w b_h,
  exact q,
end
  

