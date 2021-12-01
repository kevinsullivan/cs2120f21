/-
to prove a there exists we must first consider some thing then give a proof it fullfills the requierments
A witess is what we consider and we pair this with a proof. (even ℕ → Prop) this is a predicat.
predicats are like parameretized functions that take input and give propoistion so ev7 is a good proposition not a proof
a predicate gives rise to a whole family of propositions NOT proofs

the set that ev (n nat) := n % 2 = 0

ev is a membership predicate -> if true for set it is member otherwise it is not part of the set

less than or equal is a predicate - it takes in two different things and proposes that one is less than to the other

partial evalutation of a function
if function le takes in two variables / places 
then le _ _ is a two place
le 3 is a one place
le 3 4 is a zero place

∃ n, ev n
does there exist an n such that the proposition ev n is true
so <4,proof that 4%2 = 0> or <4,eq.rfl> show the equality is reflective, eq.refl will evaluate 4%2


Elimination rule for the proof of exists. Give name to what exists. Like w exists and we know it has properties of red and blue.

If you know it exists you can give it a name and use it as a witness.
-/

def ev (n : ℕ) : Prop := n%2=0

example : exists (n : ℕ), ev n :=
begin
  apply exists.intro _ _,
  exact 6,
  apply eq.refl,
end

def pythag_triples (a b c : ℕ ) : Prop := a*a + b*b = c*c

example : exists (a b c : ℕ ), pythag_triples 3 4 5 :=
begin
    apply exists.intro 3,
    apply exists.intro 4,
    apply exists.intro 5,
    unfold pythag_triples,
    apply eq.refl, 
end

example : exists n, ev n := _

example : exists (a b c : ℕ), a*a + b*b = c*c := 
begin
  apply pythag_triples 3 4 5,
  apply eq.refl,
end

example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end