-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5

theorem PandNotP : ∀(P : Prop), P ∧ ¬P → false := -- custom theorem for this problem
begin
  assume P,
  assume p,
  cases p,
  exact p_right p_left,
end


theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume A B,
  have a := classical.em A, 
  have b := classical.em B,
  --have aab := and.intro a b,
  apply iff.intro,
  -- forwards
    assume a1,
    cases a,
    cases b,
    --one 
    apply false.elim,
    exact a1 (and.intro a b),

    --two
    apply or.intro_right _ b,

    --three
    apply or.intro_left _ a, 
    
  -- backwards
    assume a2,
    apply not.intro,
    assume a3,
    cases a2,
    --one
    cases a3, --this is a fun shortcut for spliting up ∧ proofs
    have f := and.intro a3_left a2,
    have f2 := PandNotP A,
    exact f2 f,

    --two
    cases a3, --this is a fun shortcut for spliting up ∧ proofs
    have f := and.intro a3_right a2,
    have f2 := PandNotP B,
    exact f2 f,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  have p := classical.em P, 
  have q := classical.em Q,
  assume notpq,
  cases p,
  --cases q,
  --one
  apply false.elim,
  exact notpq (or.intro_left Q p),

  --two
  cases q,
    -- one
      apply false.elim,
      exact notpq (or.intro_right P q),
    -- two
      exact and.intro p q,  
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  --forwards
    assume ppq, 
    cases ppq,
    --one
    exact or.intro_left Q ppq,

    --two
    cases ppq,
    exact or.intro_right P ppq_right,

  --backwards
    assume pq,
    have PnotP := classical.em P,
    cases pq,
    
    --one
    exact or.intro_left _ pq,

    --two
    cases PnotP,
      -- one
        exact or.intro_left _ PnotP,
      -- two
        exact or.intro_right _ (and.intro PnotP pq),
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  --forward
    assume pqr,
    cases pqr,
    cases pqr_left,
    cases pqr_right,
    --one
    exact or.intro_left _ pqr_right, --pqr_left works here as well, case 1 and 2 are solved the same hmm?

    --two
    exact or.intro_left _ pqr_left,

    --three
      cases pqr_right,
      --one
      exact or.intro_left _ pqr_right,
        
      --two
      exact or.intro_right _ (and.intro pqr_left pqr_right),

  --backward
    assume pqr,
    cases pqr,

    --one 
    apply and.intro (or.intro_left Q pqr) (or.intro_left R pqr),

    --two 
    cases pqr,
    apply and.intro (or.intro_right P pqr_left) (or.intro_right P pqr_right),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=


begin
  assume P Q R S,
  apply iff.intro,
  --forward
    assume pqrs,
    cases pqrs with pq rs,
    cases pq,
    cases rs,
    
    --one 
      exact or.intro_left _ (and.intro pq rs),

    --two
      apply or.symm,
      --have f1 := or.intro_right (P ∧ R) (and.intro pq rs),
      --have f2 := or.intro_left ((Q ∧ R) ∨ (Q ∧ S)) f1, 
      have f1 := or.intro_left (Q ∧ R ∨ Q ∧ S) (and.intro pq rs),
      have f2 := or.intro_left (P ∧ R) (f1),
      exact f2,

    --three
    cases rs,
    --one
    apply or.symm,
    -- I need: P ∧ S ∨ Q ∧ R ∨ Q ∧ S
    have f1 := or.intro_right (P ∧ S) (or.intro_left (Q ∧ S) (and.intro pq rs)),
    have f2:= or.intro_left (P ∧ R) f1,
    exact f2,

    --two
    apply or.symm,
    have f1 := or.intro_right (P ∧ S) (or.intro_right (Q ∧ R) (and.intro pq rs)),
    have f2 := or.intro_left (P ∧ R) f1,
    exact f2,


  --backward
  assume pqr,
  cases pqr,
  
  --one
  cases pqr,
  exact and.intro (or.intro_left Q (pqr_left) ) (or.intro_left S (pqr_right) ),
  --two
  cases pqr,
  cases pqr,
  exact and.intro (or.intro_left Q pqr_left) (or.intro_right R pqr_right),

  --three
  cases pqr,
  cases pqr,
  exact and.intro (or.intro_right P pqr_left) (or.intro_left S pqr_right),

  --four 
  cases pqr,
  exact and.intro (or.intro_right P pqr_left) (or.intro_right R pqr_right),
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (p : ℕ), p ≠ 0 :=
begin
  apply exists.intro 1 _,
  assume z,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  --forwards
    --one
    assume pq,
    have p := classical.em P,
    cases p,
    have a := pq p,
    exact or.intro_right _ a,

    --two 
    exact or.intro_left _ p,

  --backwards
    assume pq,
    cases pq,
    --one
    assume p,
    apply false.elim,
    exact pq p,

    --two 
      assume p,
      exact pq,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q A B,
  have a := classical.em P,
  cases a,

  --one
  have b := A a,
  have c := B b,
  contradiction,

  --two
  exact a,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q a b,
  have c := classical.em P,
  cases c,

  --one
  exact c,

  --two
  have d := a c,
  contradiction,
end

