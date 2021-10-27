import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

variable {α : Type} 

example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  intros α L,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume xinLintL,
  have xinL := xinLintL.left,
  exact xinL,
  assume xinL,
  apply and.intro,
  exact xinL,
  exact xinL,
end 


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ ( X L : set α), X ∪ L = L ∪ X :=
begin
  assume X,
  assume L,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume xinXorL,
  apply or.elim xinXorL,
  assume xinX,
  apply or.intro_right,
  exact xinX,
  assume xinL,
  apply or.intro_left,
  exact xinL,
  assume xinLorX,
  apply or.elim xinLorX,
  assume xinL,
  apply or.intro_right,
  exact xinL,
  assume xinX,
  apply or.intro_left,
  exact xinX,
end

/-
Assume X and L are sets of type α. We must prove that
X ∪ L = L ∪ X. The first step is to convert the proof to now 
need to prove for all x of type α, x ∈ L ∪ X ↔ x ∈ X ∪ L. 
From here we can apply the introduction rule of ↔ to split
into two proofs : x ∈ L ∪ X → x ∈ X ∪ L and 
x ∈ X ∪ L → x ∈ L ∪ X. For the first proof, we assume we have a 
proof of x ∈ L ∪ X. From here we can do a case analysis of this proof
to prove x ∈ X ∪ L for x ∈ L and x ∈ X. For x ∈ L we can use the
right introduction rule for or on d to require a proof of
x ∈ L which we already have a proof of. Then, for x ∈ X, for we can use the 
left introdcution rule for on on x ∈ X ∪ L to require a proof of x ∈ X which
we already have a proof of. Thus we have proven the first implication.
For the second implication we assume a proof of x ∈ X ∪ L. From 
here we can use the elimination rule of or on x ∈ X ∪ L to have 
x ∈ L and x ∈ X. If we prove x ∈ L ∪ X for both then the overall
implication is true. Starting with x ∈ L we can apply the left introduction 
rule for or on x ∈ L ∪ X to prove x ∈ L which we already have a proof of. 
for x ∈ X we can apply the right introduction rule of or to x ∈ L ∪ X to
only prove x ∈ X which we already have a proof of. Thus the implication
is true. By proving both implications the overall ↔ is proved. QED 
-/


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

--Reflexivity
example : ∀ (L : set α), L ⊆ L :=
begin
  assume L,
  
end

--Transitivity
example : ∀ (A B C : set α), A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros A B C,
  assume asubb,
  assume asubc,
  
end 


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

--union
example : ∀ (A B C : set α), (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  intros A B C,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume xinABC,
  apply or.elim xinABC,
  assume xinAB,
  apply or.elim xinAB,
  assume xinA,
  apply or.intro_left,
  exact xinA,
  assume xinB,
  apply or.intro_right,
  apply or.intro_left,
  exact xinB,
  assume xinC,
  apply or.intro_right,
  apply or.intro_right,
  exact xinC,
  assume xinABC,
  apply or.elim xinABC,
  assume xinA,
  apply or.intro_left,
  apply or.intro_left,
  exact xinA,
  assume xinBC,
  apply or.elim xinBC,
  assume xinB,
  apply or.intro_left,
  apply or.intro_right,
  exact xinB,
  assume xinC,
  apply or.intro_right,
  exact xinC,
end

/-
Assume A B and C are sets of type α. Prove (A ∪ B) ∪ C = A ∪ (B ∪ C). 
This can be converted to say for all x of type α, x ∈ (A ∪ B) ∪ C ↔ x ∈ A ∪ (B ∪ C). 
From here apply the introduction rule for iff to seperately prove
x ∈ (A ∪ B) ∪ C → x ∈ A ∪ (B ∪ C) and x ∈ A ∪ (B ∪ C) → x ∈ (A ∪ B) ∪ C. 

First direction:
Assume a proof of x ∈ (A ∪ B) ∪ C. From this a case study of this proof 
will say that if x ∈ A ∪ (B ∪ C) can be proven for x ∈ A, x ∈ B, x ∈ C then
the overall implication is true by the or elimination rule.
x ∈ A:
Assume a proof of x ∈ A. From here apply the left or elimination rule to 
x ∈ A ∪ (B ∪ C) to only need to prove x ∈ A which we already have a proof of.
x ∈ B:
Assume a proof of x ∈ B. From here apply the right elemination rule then the 
left elimination rule of or to x ∈ A ∪ (B ∪ C) to only need a proof of x ∈ B. 
We already have a proof of this by assumption. 
X ∈ C: 
Assume a proof of x ∈ C. From here apply the right elimination rule of or to
x ∈ A ∪ (B ∪ C) twice to only need a proof of x ∈ C. We already have a proof of 
this by assumption. 
The first implication is true. 

Second direction:
Assume a proof of x ∈ A ∪ (B ∪ C). From this a case study will say that
if x ∈ (A ∪ B) ∪ C can be proven for x ∈ A, x ∈ B, and x ∈ C, the overall 
implication will also be true by the or elimination rule. 
x ∈ a: 
Assume a proof of x ∈ A. From this apply the left elimination rule of or to 
x ∈ (A ∪ B) ∪ C twice to only need a proof of x ∈ A. We already have a proof of 
this by assumption.
x ∈ B:
Assume a proof of x ∈ B. From this apply the left elimination rule and the
right elimination rule of or to x ∈ (A ∪ B) ∪ C to only need a proof of x ∈ B.
This proof already exists by assumption. 
x ∈ C:
Assume a proof of x ∈ C. From this apply the right elimination rule of or to 
x ∈ (A ∪ B) ∪ C to only need a proof of x ∈ C. This proof already exists by 
assumption. 
The second implication is true. 

By proving both directions of the ↔ the overall statement is therefore true.  
-/

--intersection
example : ∀ (A B C : set α), (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
  intros A B C,
  apply set.ext, 
  assume x,
  apply iff.intro,
  assume xinABC,
  have xinA := xinABC.left.left,
  have xinB := xinABC.left.right,
  have xinC := xinABC.right,
  have xinBC := and.intro xinB xinC,
  have xinabc := and.intro xinA xinBC,
  exact xinabc,
  assume xinABC,
  have xinA := xinABC.left,
  have xinB := xinABC.right.left,
  have xinC := xinABC.right.right,
  have xinAB := and.intro xinA xinB,
  have xinabc := and.intro xinAB xinC,
  exact xinabc,
end

/-
Assume A B and C are sets of type α. Prove (A ∩ B) ∩ C = A ∩ (B ∩ C). 
This can be rewritten as for all x of type α, 
x ∈ (A ∩ B) ∩ C ↔ x ∈ A ∩ (B ∩ C). Apply the introduction rule for 
↔ to split the proof into x ∈ (A ∩ B) ∩ C → x ∈ A ∩ (B ∩ C) and 
x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ C. 

First direction:
Assume a proof of x ∈ (A ∩ B) ∩ C. By applying the and elimination rule
to x ∈ (A ∩ B) ∩ C, proofs of x ∈ A, x ∈ B, and x ∈ C can be constructed. 
The introduction rule of and can be used on x ∈ B and x ∈ C to construct a 
proof of x ∈ B ∩ C. From here the introduction rule of and can be used again
on x ∈ A and x ∈ B ∩ C to construct a proof of x ∈ A ∩ (B ∩ C). This 
is exactly what is being proved, therefore the first implication is true. 

Second direction: 
Assume a proof of x ∈ A ∩ (B ∩ C). By applying the and elimmination rule to 
x ∈ A ∩ (B ∩ C), proofs of x ∈ A, x ∈ B, and x ∈ C can be constructed. The 
introduction rule of and can be used on x ∈ A and x ∈ B to construct a proof of
x ∈ A ∩ B. From here the introduction rule of and can be used again on x ∈ A ∩ B
and x ∈ C to construct a proof of  ∈ (A ∩ B) ∩ C. This is exactly what is 
being proved, therefore the second implication is true.

As both directions are true, the overall proof is also true. 
-/


/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example : ∀ (A B C : set α), A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C) :=
begin
  intros A B C,
  apply set.ext,
  assume x,
  apply iff.intro,
  assume xinABC,
  have xinA := xinABC.left,
  have xinB := xinABC.right.left,
  have xinC := xinABC.right.right,
  have xinAB := and.intro xinA xinB,
  have xinAC := and.intro xinA xinC,
  have xinABAC := and.intro xinAB xinAC,
  exact xinABAC,
  assume xinABAC,
  have xinA := xinABAC.left.left,
  have xinB := xinABAC.left.right,
  have xinC := xinABAC.right.right,
  have xinBC := and.intro xinB xinC,
  have xinABC := and.intro xinA xinBC,
  exact xinABC,
end 

/-
Assume A B and C are sets of type α. Prove 
A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C). This can be rewritten to say for all x of type 
α, x ∈ A ∩ (B ∩ C) ↔ x ∈ (A ∩ B) ∩ (A ∩ C). The introduction rule for ↔ can be 
applied to split this into seperate proofs of 
x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ (A ∩ C) and x ∈ (A ∩ B) ∩ (A ∩ C) → x ∈ A ∩ (B ∩ C)

First direction:
Assume a proof of x ∈ A ∩ (B ∩ C). From this, the elimination rule for and can be 
used to construct seperate proofs of x ∈ A, x ∈ B, and x ∈ C. Then the introduction 
rule for and can be used on x ∈ A and x ∈ B to create a proof of x ∈ A ∩ B. Then
the introduction rule for and can be used on x ∈ A and x ∈ C to create a proof of 
x ∈ A ∩ C. From here the introduction rule for and can be used one last time on 
x ∈ A ∩ B and x ∈ A ∩ C to create a proof of x ∈ (A ∩ B) ∩ (A ∩ C). This is what
we are trying to prove therefore the first implication is true. 

Second direction:
Assume a proof of x ∈ (A ∩ B) ∩ (A ∩ C). From this, the elimination rule for and 
can be used to construct seperate proofs of x ∈ A, x ∈ B, and x ∈ C. Then the
introduction rule for and can be used on x ∈ B and x ∈ C to construct a proof of 
x ∈ B ∩ C. From here, the introduction rule for and can be used on x ∈ A and 
x ∈ B ∩ C to create a proof of x ∈ A ∩ (B ∩ C). This is what we are trying to 
prove, therefore the second implication is true. 

Both implications are true, therefor the overall ↔ is true as well. 
-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ (A B C : set α), A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  intros A B C,
  apply set.ext,
  assume x, 
  apply iff.intro,
  assume xinABC,
  cases xinABC,
  apply and.intro,
  apply or.intro_left,
  exact xinABC,
  apply or.intro_left,
  exact xinABC,
  have xinB := xinABC.left,
  have xinC := xinABC.right,
  apply and.intro,
  apply or.intro_right,
  exact xinB,
  apply or.intro_right,
  exact xinC,
  assume xinABAC,
  have xinAB := xinABAC.left,
  have xinAC := xinABAC.right,
  cases xinAB,
  apply or.intro_left,
  exact xinAB,
  cases xinAC,
  apply or.intro_left,
  exact xinAC,
  have xinBC := and.intro xinAB xinAC,
  apply or.intro_right,
  exact xinBC,
end

/-
Assume A B and C are sets of type α. Prove A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C). 
This can be rewritten to say for all x of type α 
x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C). The introduction rule for ↔ splits this
into two proofs; x ∈ A ∪ (B ∩ C) → x ∈ (A ∪ B) ∩ (A ∪ C) and 
x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ (B ∩ C)

First direction:
Assume a proof of x ∈ A ∪ (B ∩ C). Use a case study to prove x ∈ (A ∪ B) ∩ (A ∪ C)
for x ∈ A and x ∈ B ∩ C seperately by the or elimination rule. 

x ∈ A:
Assume a proof of x ∈ A. Use the and introduction rule to split x ∈ (A ∪ B) ∩ (A ∪ C)
to seperately prove x ∈ (A ∪ B) and x ∈ (A ∪ C). For both the left introduction rule
for or can be used to only need a proof of x ∈ A which we already have. Therefore
this case is true. 

x ∈ B ∩ C:
Assume a proof of x ∈ B ∩ C. Use the elimination rule for and to create seperate proofs
of x ∈ B and x ∈ C. From here apply the and introduction rule to x ∈ (A ∪ B) ∩ (A ∪ C)
to split it into seperate proofs of x ∈ (A ∪ B) and x ∈ (A ∪ C). From here
applying the right introduction rule for or to each means it will suffice to 
prove x ∈ B and x ∈ C respectively. Proofs for both already exist, therefore
this case is true

Both cases are true, therefore the overall implication is true. 

Second direction: 
Assume a proof of x ∈ (A ∪ B) ∩ (A ∪ C). Using the elimination rule for and
seperate proofs of x ∈ A ∪ B and A ∪ C can be constructed. First do a case study
on A ∪ B to show that it suffices to prove A ∪ (B ∩ C) with x ∈ A and x ∈ B 
seperately. 

x ∈ A:
Assume a proof of x ∈ A. From here apply the left elimination rule of or to
A ∪ (B ∩ C) to only need a proof of x ∈ A. A proof of this exists by assumption,
therefore this case is true.

x ∈ B:
Assume a proof of x ∈ B. This proof alone cannot prove A ∪ (B ∩ C). Therefor we do
a case study on x ∈ A ∪ C to prove A ∪ (B ∩ C) with x ∈ A and x ∈ C seperately. 

  x ∈ A:
  Assume a proof of x ∈ A. From here apply the left elimination rule of or to
  A ∪ (B ∩ C) to only need a proof of x ∈ A. A proof of this exists by assumption,
  therefore this case is true. 

  x ∈ C:
  Assume a proof of x ∈ C. From here apply the introduction rule for and to 
  x ∈ B and x ∈ C to construct a proof of x ∈ B ∩ C. Next, apply the right
  introduction rule of or to A ∪ (B ∩ C) to show that it suffices to prove 
  x ∈ B ∩ C. This proof already exists, therefore this case is true. 

Both cases within x ∈ B were true therefore this case is true. 

Both cases are true, therefore this implication is true. 

Because both implications were true, the overall ↔ is true as well. 
-/