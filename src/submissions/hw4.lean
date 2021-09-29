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
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  --first disjunct
    assume npandq,
    have pornp := classical.em P,
    have qornq := classical.em Q,
    cases pornp,
    cases qornq,
    --case 1
      have pq := and.intro pornp qornq,
      contradiction,
    --case 2
      apply or.intro_right,
      exact qornq,
    --case 3
      apply or.intro_left,
      exact pornp,
  --second disjunct
    assume npornq,
    apply not.intro,
    assume pq,
    have p : P := and.elim_left pq,
    have q : Q := and.elim_right pq,
    cases npornq,
    have npq := and.intro npornq q,
    contradiction,
    have pnq := and.intro npornq p,
    contradiction, 
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume nporq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  --case 1
    apply and.intro,
    apply not.intro,
    assume p,
    have porq : P ∨ Q := or.inl p,
    contradiction,
    apply not.intro,
    assume q,
    have porq : P ∨ Q := or.inr q,
    contradiction,
  --case 2
    apply and.intro,
    apply not.intro,
    assume p,
    have porq : P ∨ Q := or.inl p,
    contradiction,
    apply not.intro,
    assume q,
    have porq : P ∨ Q := or.inr q,
    contradiction,
  --case 3
    apply and.intro,
    apply not.intro,
    assume p,
    have porq : P ∨ Q := or.inl p,
    contradiction,
    apply not.intro,
    assume q,
    have porq : P ∨ Q := or.inr q,
    contradiction,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  --first disjunct
    assume pornpq,
    apply or.elim pornpq,
    --left side
      assume p,
      apply or.intro_left,
      exact p,
    --right side
      assume npq,
      have q := and.elim_right npq,
      apply or.intro_right,
      exact q,
  --second disjunct
    assume porq,
    apply or.elim porq,
    --left side
      assume p,
      apply or.intro_left,
      exact p,
    --right side
      assume q,
      have pornp := classical.em P,
      cases pornp,
      apply or.intro_left,
      exact pornp,
      have pnq := and.intro pornp q,
      apply or.intro_right,
      exact pnq,  
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  --first disjunct
    assume porqporr,
    have porq := and.elim_left porqporr,
    have porr := and.elim_right porqporr,
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
        have pr := and.intro porq porr,
        apply or.intro_right,
        exact pr,
  --second disjunct
    assume porqr,
    apply and.intro,
    --left side
      cases porqr,
      --case 1
        apply or.intro_left,
        exact porqr,
      --case 2
        have q : Q := and.elim_left porqr,
        apply or.intro_right,
        exact q,
    --right side
      cases porqr,
      --case 1
        apply or.intro_left,
        exact porqr,
      --case 2
        have r : R := and.elim_right porqr,
        apply or.intro_right,
        exact r,
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
    assume porqrors,
    have porq := and.elim_left porqrors,
    have rors := and.elim_right porqrors,
    cases porq,
    cases rors,
    --case 1
      have pr := and.intro porq rors,
      apply or.intro_left,
      exact pr,
    --case 2
      have ps := and.intro porq rors,
      apply or.intro_right,
      apply or.intro_left,
      exact ps,
    --case 3  
      cases rors,
      --case 3.1
        have qr := and.intro porq rors,
        apply or.intro_right,
        apply or.intro_right,
        apply or.intro_left,
        exact qr,
      --case 3.2
        have qs :=  and.intro porq rors,
        apply or.intro_right,
        apply or.intro_right,
        apply or.intro_right,
        exact qs,
  --backward
    assume ors,
    apply and.intro,
    --left
      cases ors,
      --case 1
        have p := and.elim_left ors,
        apply or.intro_left,
        exact p,
      --case 2
        cases ors,
        --case 2.1
          have p := and.elim_left ors,
          apply or.intro_left,
          exact p,
        --case 2.2
          cases ors,
          --case 2.2.1
            have q := and.elim_left ors,
            apply or.intro_right,
            exact q,
          --case 2.2.2
            have q := and.elim_left ors,
            apply or.intro_right,
            exact q,
    --right
      cases ors,
      --case 1
      have r := and.elim_right ors,
      apply or.intro_left,
      exact r,
      --case 2
        cases ors,
        --case 2.1
          have s := and.elim_right ors,
          apply or.intro_right,
          exact s,
        --case 2.2
          cases ors,
          --case 2.2.1
            have r := and.elim_right ors,
            apply or.intro_left,
            exact r,
          --case 2.2.2
            have s := and.elim_right ors,
            apply or.intro_right,
            exact s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n : ℕ), n ≠ 0  :=
begin
  apply exists.intro 2,
  assume h,
  cases h,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  --first disjunct
    assume pimpq,
    have pornp := classical.em P,
    have qornq := classical.em Q,
    cases pornp,
    cases qornq,
    --case 1
    apply or.intro_right,
    exact qornq,
    --case 2
    have q := pimpq pornp,
    apply or.intro_right,
    exact q,
    --case 3
    apply or.intro_left,
    exact pornp,
  --second disjunct
    assume nporq,
    assume p,
    have pornp := classical.em P,
    have qornq := classical.em Q,
    cases nporq,
    cases pornp,
    cases qornq,
    exact qornq,
    contradiction,
    cases qornq,
    exact qornq,
    contradiction,
    exact nporq,



end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume nq,
  apply not.intro,
  assume p,
  have q := pimpq p,
  contradiction,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npimpnq,
  assume q,
  have pornp := classical.em P,
  cases pornp,
  --case 1
    exact pornp,
  --case 2
    have np := npimpnq pornp,
    contradiction,
end

