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

  --forward
  assume a,
  cases a,
    --1
    apply or.intro_right _ a,
    --have f := or.intro_right (A ∈ S) a, -- this is me experimenting with how these rules work, ignore
    --exact f,
    --2
    apply or.intro_left _ a,

  --backward
  assume a,
  cases a,
    --1
    apply or.intro_right _ a,

    --2
    apply or.intro_left _ a,
end

/-
English Language Proof:
To begin the proof we simply assume basic foundational knowledge such as the prescence of two sets L and S of an arbitrary type A.
(similar assumptions are made for all other proofs and for the sake of brevity are not explicitly stated in each English language proof)
If we can prove that L ∪ S → S ∪ L and S ∪ L → L ∪ S we have sufficently shown L ∪ S ↔ S ∪ L and thus  L ∪ S = S ∪ L. This is a trivial ussage of the introduction rule for ↔.
In the forward direction we consider the possible cases of L ∪ S which by the or elimination rule are case L and case S. Each of these cases is trivially solved by an application of the or introduction rule.
The backwads direction is solved in an identical manner. QED
-/

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
English Language Proof:
To prove both the reflexivity and transivity of ⊆ each property was shown individually true and combined with a simple and statement.
In the proof this was split into two halves (reflexivity and transivity respectively). Reflexivity was trivial to show as a set is always a subset of itself.
To prove that L ⊆ L (i.e reflexivity) it is assumed that we have some arbitrary 'a' that is a member of L 
and must show that the arbitrary 'a' is also a member of the set that our subset claims to be a subset of which is conviently also L. 
This is a trivial proof solved based on assumption. 

To prove transivity we assume to have proofs that L is a ⊆ of S and that S is a ⊆ of Q. To prove the subset we use our "intro" rule for subset
and show that some arbitrary 'a' that is a ∈ of L (with our other assumptions) can lead to a proof of a ∈ Q. In much the same way other transivity theorems are shown,
we can use our proof of  L ⊆ S as a function that upon recieving a proof that a ∈ L returns a proof a ∈ S. We can chain this with out proof that
S ⊆ Q to recieve a proof that a ∈ Q and thus the proof is shown. QED
-/

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
/-
English Language Proof:

To prove that (L ∪ (S ∪ Q) = (L ∪ S) ∪ Q) ∧ (L ∩ (S ∩ Q) = (L ∩ S) ∩ Q) the proof is split into two parts using the and introduction rule. (i.e if I show each part individually I have sufficently shown both part 1 and part 2)
The associative property of ∪ was shown first. By way of the introduction rule for ↔ the proof was reduced to proving the following statements
1) (L ∪ (S ∪ Q) → (L ∪ S) ∪ Q) and 2) (L ∪ S) ∪ Q) → (L ∪ (S ∪ Q). The left side was shown by using the or elimination rule (case analysis)
to further reduce the complexity of the problem. L and S ∪ Q where the two cases considered with the latter (S ∪ Q) being further reduced with a second 
case analysis to cases S and Q. In each of these three cases the requiered proof was constructed using versions of the introduction rule for or.
The lean code above shows more specific combinations with the or introduction rule. The second half of this proof (labeled 2) ) wash shown in an
identical manner.

The associative property of ∩ was shown second. The associative property of ∩ was shown first. By way of the introduction rule for ↔ the proof was reduced to proving the following statements
1) (L ∩ (S ∩ Q) → (L ∩ S) ∩ Q) and 2) (L ∩ S) ∩ Q) → (L ∩ (S ∩ Q). The left side was completed by using the and elimination rule (or case analysis)
to obtain individual proofs for a being a member of L S Q. These where recombined using the and introduction rule in the proper order (L ∩ S) ∩ Q) to complete this half of the proof.
A near identical method was used for the second half of this proof and thus QED. 

-/


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



theorem leftDistributiveOverIntersection : ∀(A : Type) (L S Q : set A) (a : A), L ∩ (S ∩ Q) = (L ∩ S) ∩ (L ∩ Q) := 
begin
  intros A L S Q a,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,

  --forward
  assume LSQ,
  cases LSQ with L SQ,
  cases SQ with S Q,
  exact and.intro (and.intro L S) (and.intro L Q),

  --backward
  assume LSQ,
  cases LSQ with LS LQ,
  cases LS with L S,
  cases LQ with L Q,
  exact and.intro L (and.intro S Q),
end
/-
English Language Proof and Statement: The left distributive property of ∩ over ∩ is that for all L S and Q of type set A where A is some arbitrary type,
L ∩ (S ∩ Q) equals (L ∩ S) ∩ (L ∩ Q). This can be proven by showing L ∩ (S ∩ Q) → (L ∩ S) ∩ (L ∩ Q) and (L ∩ S) ∩ (L ∩ Q) → L ∩ (S ∩ Q) 
as obtained by applying the introduction rule for ↔. The proof is remarkably similar to the proof of associativity of ∩ as shown above.
Each implication is solved individually. The forwards direction is solved by assuming L ∩ (S ∩ Q) and showing (L ∩ S) ∩ (L ∩ Q) follows
(this is the introduction rule for implication). From L ∩ (S ∩ Q) it can be shown that x is a ∈ of L S Q individually by applying the elimination rule for and (or cases) 
These individual proofs can be reassembled into a proof of (L ∩ S) ∩ (L ∩ Q) by applying the introduction rule for and. 
The backwards direction of this proof is nearly identical. Thus, QED.

-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

theorem leftDistributiveOverUnion : ∀(A : Type) (L S Q : set A) (a : A), L ∪ (S ∪ Q) = (L ∪ S) ∪ (L ∪ Q):=
begin
  intros A L S Q a,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,

  --forward
  assume LSQ,
  cases LSQ,

  --one
  have f1 := or.intro_left (x ∈ S) LSQ,
  exact or.intro_left _ f1,

  --two
  cases LSQ,

    --one
    have f1 := or.intro_right (x ∈ L) LSQ,
    exact or.intro_left _ f1,

    --two
    exact or.intro_right (x ∈ L ∨ x ∈ S) (or.intro_right (x ∈ L) LSQ),
  

  --backwards 
  assume LSQ,
  cases LSQ,

  --one 
  cases LSQ,
    --one
    exact or.intro_left (x ∈ S ∨ x ∈ Q) LSQ,

    --two
    exact or.intro_right (x ∈ L) (or.intro_left (x ∈ Q) LSQ),

  --two
  cases LSQ,

  --one 
  exact or.intro_left (x ∈ S ∨ x ∈ Q) LSQ,

  --two
  exact or.intro_right (x ∈ L) (or.intro_right (x ∈ S) LSQ),
end

/-
English Language Proof and Statement:
The left distributive property of ∪ over ∪ is that for all L S and Q of type set A where A is some arbitrary type,
L ∪ (S ∪ Q) equals (L ∪ S) ∪ (L ∪ Q). This can be proven by showing L ∪ (S ∪ Q) → (L ∪ S) ∪ (L ∪ Q) and (L ∪ S) ∪ (L ∪ Q) → L ∪ (S ∪ Q) 
as obtained by applying the introduction rule for ↔. The proof is remarkably similar to the proof of associatiity of ∪ as shown earlier.
Each implication is solved individually. The forwards direction is solved by assuming L ∪ (S ∪ Q) and showing (L ∪ S) ∪ (L ∪ Q) follows
(this is the introduction rule for implication). To show this, we look at possible cases for L ∪ (S ∪ Q) which are cases L and S ∪ Q.
S ∪ Q is further analyzed by cases into S and Q. These thre cases (x ∈ L x ∈ S and x ∈ Q) are solved individually by applying 
the introduction rule of or to create the desired result. More details on these cases can be found in the lean code above. 
The backwards direction is solved in a simlar manner, however, with more cases (4 not 3). Thus, QED.

-/


