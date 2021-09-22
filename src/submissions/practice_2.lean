/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

/-
true is true through the introduction rule for true
-/

example : false := _    -- trick question? why?
--There is no way to prove false because proving false would make it true

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward direction
    assume porp, 
    apply or.elim porp,
    --left disjunct
      assume p,
      exact p,
    --right disjunct
      assume p,
      exact p,
  --backward direction
    assume p,
    apply or.intro_right,
    exact p,
end

/-
Assume P is a proposition of an arbitrary type. By the introduction rule of 
if and only if, P ∨ P ↔ P can be split to P ∨ P → P and P → P ∨ P. 
Forward direction
First assume you have a proof of P ∨ P. The elimination rule of P allows you to
further split that and prove P → P for the left side and P → P for the right side.
for both you assume you have a prop of P. Thus the assumption of P is exactly
P which is always true.
Backward direction
First assume you have a proof of P. Then by the introduction rule of or applied to 
the left side of P ∨ P and having a proof of P, you have a proof of P ∨ P.
Thus, the proposition P ∨ P ↔ P is proven QED.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume pandp,
    have pleft : P := and.elim_left pandp,
    exact pleft,
  --backwards
    assume p,
    apply and.intro,
    --left
      exact p,
    --right
      exact p,
end

/-
Assume P is a proposition of an arbitrary type. By applying the introduction
rule of iff, the proposition can be split into  P ∧ P → P and P → P ∧ P. 
Forward direction
First assume a proof of P ∧ P. By the elimination rule of and applied to the left
side of P ∧ P, you have a proof of P. Thus P is exactly P and this evaluates to 
true. 
Backward direction
Assume you have a proof p of P. Using the introduction rule of and, you can split
the P ∧ P that needs to be proved into two seperate propositions of P and P. Proving
both will in turn prove P ∧ P. both of the Ps are proved by exact p, therefore the
implication is true.
By proving both sides of the implication, the overall iff is true. QED
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
    assume porq,
    apply or.elim porq,
    --left disjunct
      apply or.intro_right,
    --right disjuncth
      apply or.intro_left,
  --backward
    assume qorp,
    apply or.elim qorp,
    --left disjunct
      apply or.intro_right,
    --right disjunct
      apply or.intro_left,
end

/-
Assume P and Q are propositions of an arbitrary type. Apply the introduction rule
of iff to split the original prop to P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q. 
Forward direction
Assume a proof of P ∨ Q. Apply the elimination rule of or to further split the
prop to P → Q ∨ P and Q → Q ∨ P. 
First Disjunct
assume a proof of P. Apply the introduction rule of or to the right side of 
Q ∨ P leaving only P. P is exactly P
Second Disjunct
Assume a proof of Q. Apply the introduction rule of or to the left side of Q ∨ P. 
This leaves just Q which is exactly true
backward Direction
Assume a proof of Q ∨ P. Apply the elimination rule of or to further split the
prop to Q → P ∨ Q and P → P ∨ Q. 
First Disjunct
Assue a proof of Q. Apply the introduction rule of or to the right side of 
P ∨ Q to leave just Q. Q is exactly Q
Second Disjunct
Assume a proof of P. Apply the introdcution rule of or to the left sdie of 
P ∨ Q to leave juse P. P is exactly P.
Proving both sides of the implies proves the overall iff. QED
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
    assume pandq,
    have p : P := and.elim_left pandq,
    have q : Q := and.elim_right pandq,
    have qp : Q ∧ P := and.intro q p,
    exact qp,
  --backward
    assume qandp,
    have q : Q := and.elim_left qandp,
    have p : P := and.elim_right qandp,
    have pq : P ∧ Q := and.intro p q,
    exact pq,
end

/-
Assue P and Q are propositions of an arbitrary type. Apply the introduction rule 
of iff to the original proposition to split it into P ∧ Q → Q ∧ P and
Q ∧ P → P ∧ Q
Forward Direction
Assume a proof of P ∧ Q. By the elimination rule of each side of P ∧ Q, you have
a proof of P and Q seperately. Then, by applying the introduction rule of 
and you can create a proof of Q ∧ P which is exactly Q ∧ P. 
Backward Direction
Assume a proof of Q ∧ P. By the elimination rule of each side of Q ∧ P, you have
a proof of Q and P seperately. Then, by applying the introduction rule of 
and you can create a proof of P ∧ Q which is exactly P ∧ Q. 
Thus, by proving each implication of iff, the overall prop is true. QED
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forward
    assume pandqorr,
    have p : P := and.elim_left pandqorr,
    have qorr : Q ∨ R := and.elim_right pandqorr,
    apply or.elim qorr,
    --first disjunct
      assume q,
      have pq : P ∧ Q := and.intro p q,
      apply or.intro_left,
      exact pq,
    --second disjunct
      assume r,
      have pr : P ∧ R := and.intro p r,
      apply or.intro_right,
      exact pr,
  --backward
    assume pandqorpandr,
    apply or.elim pandqorpandr,
    --first disjunct
      assume pq,
      have p : P := and.elim_left pq,
      have q : Q := and.elim_right pq,
      apply and.intro _ _,
      --left
        exact p,
      --right
        apply or.intro_left,
        exact q,
    --second disjunct
      assume pr,
      have p : P := and.elim_left pr,
      have r : R := and.elim_right pr,
      apply and.intro,
      --left
        exact p,
      --right
        apply or.intro_right,
        exact r,
end

/-
Assume P Q and R are propositions of an arbitrary type. Apply the introduction 
rule of iff to the prop to split it into P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) and
(P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R). 
Forward Direction
Assume a proof of P ∧ (Q ∨ R). By the elimination rule of and applied to each side
of this proof, you have a proof of P and Q ∨ R. Apply the elimination rule
of Q ∨ R to further split the proof to Q → (P ∧ Q) ∨ (P ∧ R) and
R → (P ∧ Q) ∨ (P ∧ R). 
First Disjunct
Assume a proof of Q. By the introduction rule of and, a proof of P ∧ Q can be created. 
Apply the left introduction rule of or to (P ∧ Q) ∨ (P ∧ R) to only need to prove 
P ∧ Q. There is a proof of P ∧ Q already.
Second Disjunct
Assume a proof of R. By the introduction rule of and, a proof of P ∧ R can be created. 
Apply the right introduction rule of or to (P ∧ Q) ∨ (P ∧ R) to only need to prove
P ∧ R. There is a proof of P ∧ R already.
Backward Direction
assume a proof of (P ∧ Q) ∨ (P ∧ R). Apply the elimination rule of or to (P ∧ Q) ∨ (P ∧ R)
to split it to prove P ∧ Q → P ∧ (Q ∨ R) and P ∧ R → P ∧ (Q ∨ R). 
First Disjunct
Assume a proof of P ∧ Q. Apply the and elimination rule to both sides of P ∧ Q to get 
a proof of P and Q seperately. Next apply the and elimination rule to P ∧ (Q ∨ R) to 
split it to prove P and Q ∨ R seperately
Left (P)
A proof of P already exists and P is exactly P.
Right (Q ∨ R)
Apply the or introduction rule to the left side of Q ∨ R to only need to prove Q. 
A proof of Q already exists and Q is exactly Q. 
Second Disjunct
Assume a proof of P ∧ R. By the introduction rule of and a proof of P and R seperately
can be generated seperately. Then apply the eliminaiton rule of or to P ∧ (Q ∨ R) to 
need to prove P and Q ∨ R seperately
left (P)
A proof of p exists and P is exactly P.
Right (Q ∨ R)
Apply the or introduction rule to the right side of Q ∨ R to only need to prove R. 
A proof of R already exists and R is exactly R.
By proving both implicaitons of the iff, the overall iff is true. QED
-/


example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forward
    assume porqandr,
    apply or.elim porqandr,
    --first disjunct
      assume p,
      apply and.intro,
      --left
        apply or.intro_left,
        exact p,
      --right
        apply or.intro_left,
        exact p,
    --second disjunct
      assume qr,
      have q : Q := and.elim_left qr,
      have r : R := and.elim_right qr,
      apply and.intro,
      --left 
        apply or.intro_right,
        exact q,
      --right
        apply or.intro_right,
        exact r,
  --backward
    assume porqandporr,
    have porq : P ∨ Q := and.elim_left porqandporr,
    have porr : P ∨ R := and.elim_right porqandporr,
    cases porq,
    cases porr,
    --case 1
      apply or.intro_left,
      exact porq,
    --case 2
      apply or.intro_left,
      exact porq,
    --case 3
      cases porr,
      --case 1
        apply or.intro_left,
        exact porr,
      --case 2
        apply or.intro_right,
        have qr : Q ∧ R := and.intro porq porr,
        exact qr,
end

/-
Assume P Q and R are propositions of an arbitrary type. Apply the introduction rule of 
iff to the prop to split it to P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) and
(P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R). 
Forward Direction
Assume you have a proof of P ∨ (Q ∧ R). Apply the elimination rule of or to P ∨ (Q ∧ R)
to split it to prove P →  (P ∨ Q) ∧ (P ∨ R) and Q ∧ R → (P ∨ Q) ∧ (P ∨ R). 
First Disjunct
Assume a proof of P. Apply the and introduction rule to (P ∨ Q) ∧ (P ∨ R) to seperately
prove P ∨ Q and P ∨ R
Left
Apply the or introduction rule to the left side of P ∨ Q to only need to prove P. 
P is exactly P and a proof of P already exists
Right
Apply the or introduction rule to the left side of P ∨ Q to only need to prove P. 
P is exactly P and a proof of P already exists
Second Disjunct
Assume a proof of Q ∧ R. By the introduction rule of and you then have a proof of Q
and R seperately. Apply the and introduction rule to (P ∨ Q) ∧ (P ∨ R) to seperately
prove P ∨ Q and P ∨ R.
Left
Apply the or introduction rule to the right side of P ∨ Q to only prove Q. Q is 
exactly Q and a proof of Q already exists
Right
Apply the or introduction rule to the right side of P ∨ R to only prove R. R is 
exactly R and a proof of R already exists. 
Backward Direction 
Assume a proof of (P ∨ Q) ∧ (P ∨ R). By the introduction rule of and, proofs of 
P ∨ Q and P ∨ R exist. From here, we will examine a case study of these two if statements
Case 1
In the first case you are given a proof of P. Apply the or introduction rule to the 
left side of P ∨ (Q ∧ R) to only prove P. P is exactly P and a proof of P already exists
Case 2
In the second case you are given proofs of P and R. Apply the or introduction rule to the 
left side of P ∨ (Q ∧ R) to only prove P. P is exactly P and a proof of P already exists. 
Case 3 
Assume you are given proofs of P ∨ R and Q. From here look at a case study of this
Case 3.1 
You are given proofs of P and R. Apply the or introduction rule to the left side of
P ∨ (Q ∧ R) to only prove P. P is exactly P and a proof of P already exists.
Case 3.2 
You are given proofs of Q and R. Apply the or introduction rule to the right side of 
P ∨ (Q ∧ R) to only prove Q ∧ R. By the and introduction rule a proof of Q ∧ R
is generated. Q ∧ R is exactly Q ∧ R and a proof of Q ∧ R exists
By proving both implications of the iff, the overall iff is true. QED
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
    assume pandporq,
    have p : P := and.elim_left pandporq,
    have porq : P ∨ Q := and.elim_right pandporq,
    exact p,
  --backward
    assume p,
    apply and.intro,
    --left
      exact p,
    --right
      apply or.intro_left,
      exact p,  
end

/-
Assume P and Q are propositions of an arbitrary type. Apply the iff introduction
rule to split the prop into P ∧ (P ∨ Q) → P and P →  P ∧ (P ∨ Q). 
Forward Direction
Assume a proof of P ∧ (P ∨ Q). By the and elimination rules of each side there are
proofs of P and P ∨ Q. P is exactly P and a proof of P exists.
Backward
Assume a proof of P. Apply the and introduction rule to P ∧ (P ∨ Q) to split it and 
seperately prove P and P ∨ Q. 
Left
P is exactly P and a proof of P already exists
Right 
Apply the or introduction rule to the left side of P ∨ Q to only prove P. P is
exactly P and a proof of P already exists
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
    assume porpandq,
    apply or.elim porpandq,
    --left
      assume p,
      exact p,
    --right
      assume pandq,
      have p : P := and.elim_left pandq,
      exact p,
  --backward
    assume p,
    apply or.intro_left,
    exact p,
end

/-
Assume P and Q are propositions of an arbitrary type. Apply the iff introduction rule to 
split the prop to be P ∨ (P ∧ Q) → P and P → P ∨ (P ∧ Q)
Forward
Assume a proof of P ∨ (P ∧ Q). Apply the elimination rule of or to seperately prove
P → P and P ∧ Q → P. 
left
Assume a proof of P. P is exactly P and a proof of P exists.
Right
assume P ∧ Q. By the introduction rule of and, a proof of P exists. P is exactly P and a 
proof of P exists
Backward
assume a proof of P. Apply the introduction rule of or to the left side of P ∨ (P ∧ Q). 
P is exactly P and a proof of P exists
Both sides of the implication are true there for the iff is also true. QED
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume port,
    exact true.intro,
  --backward
    assume t,
    apply or.intro_right,
    exact true.intro,
end

/-
Assume P is a proposition of an arbitrary type. Apply the iff introduction rule to split
the prop into P ∨ true → true and true → P ∨ true
Forward
assume a proof of P ∨ true. true is true by the introduction rule of true
Backward
Assume a proof of true. Apply the or introduction rule to the right side of P ∨ true
to only prove true. True is true by the introduction rule of true. 
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume porf,
    cases porf,
    exact porf,
    cases porf,
  --backward
    assume p,
    apply or.intro_left,
    exact p,
end

/-
Assume P is a proposition of an arbitrary type. Apply the iff introduction rule to split
the prop into P ∨ false → P and P → P ∨ false
Forward
assume a proof of P ∨ false. Examine the cases of P ∨ false
Case 1
assume a proof of P. P is exactly P.
Case 2
Assume a proof of false. This is not possible so the only option is case 1
Bacward
assume a proof of P. apply the introduction rule of or to the left side of P ∨ false to 
only prove P. P is exactly P.
By proving both implications, the overall iff is true. QED
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume pandt,
    have p : P := and.elim_left pandt,
    exact p,
  --backward
    assume p,
    have t : true := true.intro,
    have pandt : P ∧ true := and.intro p t,
    exact pandt,
end

/-
Assume P is a proposition of an arbitrary type. apply the introduction rule of iff to 
split the prop into P ∧ true → P and P → P ∧ true.
Forward
assume a proof of P ∧ true. By the elimination rule of and applied to the left side of
P ∧ true, a proof of P is created. P is exactly P.
backward
Assume a proof of P. A proof of true can be created by the introduction rule of true.
By the introduction rule of and a proof pt of P ∧ true can be created. pt is
exactly P ∧ true. 
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume pandf,
    cases pandf,
    exact pandf_right,
  --backward
    assume f,
    cases f,
end

/-
Assume P is a proposition of an arbitrary type. apply the introduction rule of iff to 
the prop to split it to P ∧ false → false and false → P ∧ false. 
Forward
assume a proof of P ∧ false. Examine the cases of P ∧ false. false is the right
case of P ∧ false so P ∧ false → false is true. 
Backward
assume a proof of false. looking at cases of false, false → P ∧ false is true. 
Both implications are true therefore the overall iff is true. QED
-/
