/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
             pf: Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume pimpq,
  assume p,
  have q := pimpq p,
  exact q,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- the introduction rule for true is that a proof of true always exists

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 
begin
  exact true.intro,
end

-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Given arbitrary propositions P and Q as well
-- as a proof of both P and Q. From these two 
-- proofs a proof of P ∧ Q can be constructed

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/

/-
Left elimination:
(P Q : Prop) (P ∧ Q)
--------------------- 
        (pf : P)

Given a proof of P ∧ Q and P and Q are both propositions,
one can get a proof of P by left elimination.

Right elimination:
(P Q : Prop) (P ∧ Q)
--------------------
      (pf : Q)

Given a proof of P ∧ Q and a proof that P and Q are propositions,
one can get a proof of P by right elimination. 
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume qandp,
  have p := qandp.right,
  exact p, 
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- to prove a for all, you assue an arbitrary object
-- of an arbitrary type. If you prove the proposition
-- for that object and type then the propsition
-- holds true for all objects and types

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                       t : Q

-- If T is a type and Q is a proposition and there exists
-- a proof that for all t of type T, Q is true then for
-- a specific object t of type T, Q is true. 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

pf is like a function, which takes in an argument of type
T and returns a proof of q. Because we are given an 
argument (t : T), we can plug it into pf to get
a proof of Q. 
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- add answer here
  (Lynn : Person)
  -- add answer here
  (LL : KnowsLogic Lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀ (Lynn : Person) (LL : KnowsLogic Lynn), BetterComputerScientist Lynn := 
begin
  intros,
  exact LogicMakesYouBetterAtCS Lynn LL,
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := ¬P → (P → false) -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/-
Assume a proof of P and show that there is no way
for such a proof to exists. This proves that 
P implies false and thus ¬P
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume not P and show that not P is false.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation introduction
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classically valid, and that accepting the axiom
of the excluded middle suffices to establish negation
proof (better called double negation proof)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → (Q ↔ P) :=
begin
  assume P Q,
  assume h,
  have pimpq := iff.elim_left h,
  have qimpp := iff.elim_right h,
  apply iff.intro,
  --forward
    exact qimpp,
  --backward 
    exact pimpq,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 

/-
For the type Person, the person can be talented and a person can be nice
and a person can like another person. For all people who are nice and talented
they are liked by everyone. John Lennon is a person and John Lennon is nice and 
Talented. Therefore everyone likes John Lennon
-/
    

example : ELJL :=
begin
  unfold ELJL,
  intros,
  have JLN := JLNT.left,
  have JLT := JLNT.right,
  exact elantp JohnLennon JLN JLT p,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    heavy and red
    heavy and blue
    light and red
    light and blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y ↔ y = x 

def eq_is_transitive : Prop := 
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := ∀ (P : Prop), ¬¬P ↔ P ∨ ¬ P

example : (negelim_equiv_exmid) :=
begin
  unfold negelim_equiv_exmid,
  assume P,
  apply iff.intro,
  --forward
  assume nnp,
  have pornp := classical.em P,
  exact pornp,
  --backward
  assume pornp,
  cases pornp,
  --case 1
    apply not.intro,
    assume np,
    contradiction,
  --case 2
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∀ (p : Person), ∃ (q : Person), Loves p q) → 
          (∃ (p : Person), ∀ (q : Person), Loves p q):= 
begin
end
