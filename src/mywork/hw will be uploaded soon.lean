example: 0 ≠ 1 :=
begin
  assume a, --intro rule for negation. This means ¬ (0=1) or (0=1) → false
  cases a, --for all possible proofs of 0 = 1 it is empty and therefore implies false
end

example : 0 ≠ 0 → 2 = 3 :=
begin
  assume a,
  apply false.elim; -- does false.elim know that 2 ≠ 3? 
  apply a (eq.refl 0), -- you can also use the contradiction tactic. Looks for a proof of false or p and not p
end 

example : ∀ (P : Prop), P → ¬ ¬ P :=
begin
  assume p b c, --not not p is not p implies false then (p implies false) implies false
  --have a : p ∧ ¬p := and.intro b c, -- contradiction
  --have f := c b, or do this and apply f.
  contradiction, -- there could also be case analysis to show no proofs of false
end  
axioms em : ∀ (p : Prop), p ∨ ¬p
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume p,
  assume h,
  have ponp := classical.em p,
  cases ponp with p pn,
  assumption, -- proof is in my list of assumptions
  contradiction,
  -- we have nothing to apply our function h to
  -- we have nothing to work with

end -- this works in classical reasoning but this is not valid in leand constructive logic
-- given the current axioms we can not prove this, we need to define this as an axiom. We can have it and we can not have this as an axiom

-- axioms em : ∀ (p : Prop), p ∨ ¬p only use this if you want classical reasoning 
--the hw will need this exclusion of the middle axiom
-- using case analysis comes from a disjunction


