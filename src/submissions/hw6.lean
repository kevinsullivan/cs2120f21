import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

theorem LintersectLequalsL : ∀ (A : Type) (L : set A), L ∩ L = L :=
begin
  intros A s,
  apply set.ext _,  
  assume a,
  apply iff.intro _ _,

  --1
  assume m,
  cases m,
  exact m_left,

  --2
  assume m,
  exact and.intro m m,
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

theorem UnionCommutative : ∀ (A : Type) (L S : set A), L ∪ S = S ∪ L :=
begin
  intros A L S,
  apply set.ext _,
  assume A,
  apply iff.intro _ _,

  --1
  assume a,
  cases a,
    --1
    apply or.intro_right _ a,
    --have f := or.intro_right (A ∈ S) a, -- this is me experimenting with how these rules work, ignore
    --exact f,
    --2
    apply or.intro_left _ a,

  --2
  assume a,
  cases a,
    --1
    apply or.intro_right _ a,

    --2
    apply or.intro_left _ a,
end

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

theorem subsetReflexiveAndTransitive : ∀ (A : Type) (L S Q : set A), (L ⊆ L) ∧ (L ⊆ S → S ⊆ Q → L ⊆ Q) :=
begin
  intros A L S Q,
  apply and.intro _ _, --split would work here aswell and be more advanced I guess
  --left
  --assume a b, 
  --exact b, -- this is the longer way to do it.
  trivial, --this works as well which is pretty neat and more concise 

  --right
  assume LS SQ a Q,
  have AS := LS Q,
  have AQ := SQ AS,
  exact AQ,  
end


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

theorem UnionAndIntersectAssociative : ∀ (A : Type) (L S Q : set A), (L ∪ (S ∪ Q) = (L ∪ S) ∪ Q) ∧ (L ∩ (S ∩ Q) = (L ∩ S) ∩ Q):=
begin
  intros A L S Q,
  apply and.intro _ _,
  --left
  apply set.ext _,
  assume a,
  apply iff.intro _ _,
  --one 
  assume AL,
  cases AL,
    --one
    have f1 := or.intro_left (a ∈ S) AL,
    have f2 := or.intro_left (a ∈ Q) f1,
    exact f2,

    --two
    cases AL,
    have f1 := or.intro_right (a ∈ L) AL,
    have f2 := or.intro_left (a ∈ Q) f1,
    exact f2,

    have f1 := or.intro_right (a ∈ L ∨ a ∈ S) AL,
    exact f1,

  --two
  assume AL,
  cases AL,
    --one
    cases AL,
    have f1 := or.intro_left (a ∈ S ∨ a ∈ Q) AL,
    exact f1,

    have f1 := or.intro_right (a ∈ L) (or.intro_left (a ∈ Q) AL),
    exact f1,

    --two
    have f1 := or.intro_right (a ∈ L) (or.intro_right (a ∈ S) AL),
    exact f1,

  --right
  apply set.ext _,
  intros a,
  apply iff.intro _ _,

  --forward
  assume LSQ,
  cases LSQ with L SQ,
  cases SQ with S Q,
  exact and.intro (and.intro L S) Q,

  --backward
  intros LSQ,
  cases LSQ with LS Q,
  cases LS with L S,
  exact and.intro L (and.intro S Q),
end

--this was just an expiremnt, ignore
lemma experiment : ∀(A : Type) (L S Q : set A) (a : A), (a ∈ L ∧ a ∈ S) ∧  a ∈ Q → a ∈ L ∩ S ∩ Q :=
begin 
  intros A L S Q a LS,
  exact LS,
end

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


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


