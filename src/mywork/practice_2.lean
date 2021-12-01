/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro 

example : false := -- I cannot answer this with a proof, it does not exist. trick question? why? It is a type which has no values, uninhabbited. 
-- to be false is to have no proofs

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


