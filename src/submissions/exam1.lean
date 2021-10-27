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
             (q : Q)
     
    In English: Given a proposition P and implication P → Q,
    a proof of Q can be derived from the proof of P → Q by applying the proof of P → Q to the proof of P.
    We may translate the statement P → Q to If P then Q. Thus, if given some P we can ascertain Q.

    In constructive logic, given some implication P → Q, it is treated as a function
    where upon recieving a proof of P, returns a proof for Q similar to a ∀ statement. 
    Lean treats P → Q as a function with one input (proof of P) and one output (proof of Q).
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q pq p,
  exact pq p,
end

-- Extra credit [2 points]. Who invented this principle?

-- I believe Greek Philosipher Aristotle invented the principle of implication's elimination rule
-- calling it "modus ponens".  

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

The introduction rule for true is that it is simply, by defenition, true. For any proposition true,
it will be true and the proof of this is trivial. Thus any goal true
can be trivially solved by invoking the introduction rule for true. 

In constructive logic, true's introduction rule is represented by a proof for true
called true.intro in lean. Envoking this on any goal of true will prove and resolve the goal. 


ELIMINATION

Give an English language description of the
elimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro 

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

-- Given a proof of proposition P and a proof of proposition Q, a proof can be constructed for P ∧ Q. 
It effectively lets us combine two smaller proofs into a larger, conjoined proof of P ∧ Q 
that states both are true. This makes intuitive sense as if P is true and Q is true, then P ∧ Q must be true.

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.

Inference form:

(P Q : Prop) (pq : P ∧ Q)
--------------------------- elim_left
(p : P)
--------------------------- elim_right
(q : Q)

English form: Given a proof of P ∧ Q, the proof can be deconstructed into smaller proofs for either
P or Q. If we know that P ∧ Q is true, then we know that P and Q must be independently true.

In constructive logic, P ∧ Q is a proof of two smaller units - a proof of P and a proof of Q.
These two smaller proofs can be abtained by eliminating one side of the proof of P ∧ Q leaving
either a proof of P or a proof of Q depending on what side was "eliminated".  
The left elimination rule of ∧ returns a proof for the left side of the conjunction (in this case P) 
while the right elimination rule returns a proof for the right side of the conjuction (in this case Q).

-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), (Q ∧ P) → P := 
begin
  assume P Q PaQ,
  exact and.elim_right PaQ, 
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- To prove ∀ (t : T), Q or any other valid ∀ statement, some arbitrary t can be assumed.
From this t it must be proved that Q follows. The introduction rule of ∀ allows us to
assume an arbitrary t (or any other relevant, arbitrary variable) and then show Q follows from this assumption. 
Showing that Q follows from an arbitrary t is sufficent proof for a ∀ statement.
It is similar to the introduction rule for implication and the proof strategy is remarkably similar.

In constructive logic, ∀ is similar to a function that recieves some t of type T and returns Q. If it can
be shown that such a function is definable, then you have proven the ∀.    

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (q : Q) 

-- English language answer: ∀ has an elimination rule that lets us take a general statement
about an object and apply it to a specific case. If I know that for all natural numbers that have a 
remainder of 0 when divided by two that natural number is even, then I can look at a specific natural number
that has a zero remainder when divided by 2 (such as 4) and conclude it is even.  

In constructive logic a ∀ statement can be considered (and in lean literally is) a function that
upon recieving a t of type T, returns a proof Q. 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- If we know that in the general case objects of type T have property Q, we can take
the generalization and apply it specifically to one given object of type T.  
-- in lean this would look like: have proofOfQ := pf t,
pf (i.e the ∀ statement) is a function that when given an input of t, returns a proof of Q.
Therefore, pf t returns a proof of Q. 
This is similar to the elimination rule for implications. 
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
  (Lynn : Person)
  (LynnLogic : KnowsLogic Lynn)
/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn := 
begin 
  apply LogicMakesYouBetterAtCS Lynn,
  exact LynnLogic,
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
def not (P : Prop) := P → false  -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- The proof strategy involves showing that ¬P is true by showing 
-- the logically equivelent statement P → false is true. 
-- By the introduction rule of implications, this is simplified into assuming P and showing some
-- contradiction by way of this assumption occurs, therefore P → false and therefore ¬P has been proven. 

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that ¬P → false.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elemination
to that result to arrive at a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is clasically valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double negation elimination)
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
-- ↔ was used over → in the example below for completness and to show the communitive property works both ways
example : ∀ (P Q : Prop), (P ↔ Q) ↔ (Q ↔ P) :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
    assume pq,
    have p := iff.elim_left pq,
    have q := iff.elim_right pq,
    exact iff.intro q p,

  --backwards
  assume qp,
  have q := iff.elim_left qp,
  have p := iff.elim_right qp,
  exact iff.intro p q,
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
For all persons, there may be some who are nice or talented, and some people like other people.
For all persons, if a person is nice as well as talented, all persons (including themself) will like them.
John Lennon is a person who is both nice and talented; everyone likes John Lennon. 

Given these truths, it can be shown that everyone likes John Lennon as seen in the proof below.   
-/    

example : ELJL :=
begin
  unfold ELJL,
  introv _ _,
  apply elantp JohnLennon JLNT.left,
  exact JLNT.right,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 2 x 2 = 4
-- list the cases (informaly)
    -- heavy red
    -- heavy blue
    -- light red
    -- light blue 
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
  ∀ (T : Type) (x y : T), x = y → y = x

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

def negelim_equiv_exmid : Prop := 
  ∀(P : Prop), (¬¬P  ↔ P ) ↔ (P ∨ ¬ P)
  
example : negelim_equiv_exmid :=
begin
  unfold negelim_equiv_exmid,
  assume P,
  apply iff.intro,
  --forwards
    assume pp,
    exact classical.em P,

  --backwards
    assume pp,
    apply iff.intro,
    --one
    assume np,
    cases pp,
    exact pp,
    
    --two
    apply false.elim,
    exact np pp,
    cases pp,
      --one
        assume p,
        trivial, 
      --two 
      assume np,
      contradiction,
end
/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop
axiom LoveRefl : ∀ (p1 p2 : Person), Loves p1 p2 → Loves p2 p1


example : (∃ (P2 : Person), ∀ (P1 : Person), Loves P1 P2) → (∃ (P3 : Person), ∀ (P4 : Person), Loves P3 P4) := 
begin
  assume p,
  cases p,
  --have t := exists.intro p_w p_h,
  apply exists.intro p_w,
  assume p4,
  have loves := p_h p4,
  have refl := LoveRefl p4 p_w,
  apply refl loves,
end
