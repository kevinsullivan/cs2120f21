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
    
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  --forward
    
end

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

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  --forward
    assume porf,
    cases porf,
    exact porf_right,
  --backward
    assume f,
    cases f,
end


