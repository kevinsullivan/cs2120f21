/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

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
    exact p,
    exact p,
end

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
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


