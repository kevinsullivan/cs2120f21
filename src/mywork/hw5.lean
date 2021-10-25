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
-/

/-
If there is a function that maps every α value with
property p to a β value with property q and there exists
a value a of type α with property p then there exists a 
value b of type β with property q.
-/

/-
informal proof:

Assume there exists a mapping of type α to type β such
that for all α with property p there is a β with property q.
Also assume that there exists an α with property p. Apply the 
mapping onto the a of type α to produce b of type β. Because
a has the property p it follows that b has the property q. 
Therefore it is true there exsists some b of type β with
property q. 

-/


-- Give your formal proof here
begin
  assume h1,
  assume h2,
  cases h1,
  cases h2,
  apply exists.intro,
  have a := h1_h h2_w,
  have b := a h2_h,
  have B := h1_w h2_w,
  exact b,
end
  

