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
  assume (P),
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
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
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


