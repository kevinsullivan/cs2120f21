--Negation

/- 
Given a proposition, P, we can form a new proposition, usually written as ¬ P,
which we pronounce as "not P," and which we can define in such a way as to asert
that P is not true.
-/

/-
So waht does it mean when we say that *it is true that P is not true?*
-/

/-
First, if ¬ P is true, there should be a proof of it. Second,
what that proof should show is that *there cna be no proof of p*
-/

/-
So the way we're going to say ¬ P is to say if P were true then something
that is completely impossible would happen. Because the impossible
cannot happen, therefore there must be no proof of P.
-/

/-
What we're going to take as "the impossible thing" is that there is a proof of 
false. Have degined false to be exactly a proposition with no proofs
(otherwise it'd be true), so to have a proof of false is an impossibility.
-/

example : false → false :=
begin
  assume f,
  exact f,
end

example : false → true :=
begin
  assume f,
  exact true.intro,
end

example : true → true :=
begin
  assume t,
  exact true.intro,
end

example : true → false :=
begin
  assume t,
  --can't prove false
  --stuck
end

/-
It's this analysis that leads to the defenition of ¬P. For any proposition P, we *define* 
¬P to be the proposition, P → false. What this means that if htere is a proof of P → false, 
then you can conclude (by defenition) ¬P. This is the introduction rule for ¬.
-/

example : ¬ (0 = 1) :=
begin
  assume h,
  cases h,
end

theorem false_elim (P : Prop) (f : false) : P :=
begin
  exact false.elim f,
end