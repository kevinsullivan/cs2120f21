/-
UPDATE: Test distributed after class on 
Monday. Monday will be a review day. The
test is due back Wednesday before class.
In class Wednesday we will have at least
a short quiz to sanity check what you will
have submitted for the test. We reserve the
right to do follow-on in-person testing if
the results indicate a possible problem.
-/

/-
REVIEW: Last time we focused on the question, 
how do we construct a proof of ∃ x, P x.  

To do so, you apply the introduction rule for
exists. It's called exists.intro in Lean. You
apply it to two arguments: a specific value, w,
in place of x, and a proof that that particular
w satisfies the predicate, P, i.e., that there 
is a proof of the proposition, P w. 

In other words, you can think of a proof of
∃ x, P x, as a pair, ⟨w, pf ⟩, where w is a
witness and pf is a proof of P w.
-/

/-
Today we'll delve deeper into the mysteries
of exists elimination, or how you can *use*
a proof of ∃ x, P x.

Here's the idea: If you have a proof, ex, of
of ∃ (x : X), P x, you can apply exists.elim
to ex, and (after a few more simple maneuvers)
have yourself a specific value, (w : X), and 
a proof that w satisfies P, i.e., (pf : P w). 
The idea is that you can then uses the values
in your subsequent proof steps.

Why does this rule make sense? Consider a very
simple example. If I tell you there exists some
green ball, you can say, "well, call it b," and
give that we know it's green, we also know that
it satisfies the isGreen _ predicate, so we can
also assume we have a proof of (isGreen b). In
this example, b is a witness to the fact that
some object satisfies the predicate. The proof
then shows for sure that that is so.
-/

example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff _,
  exact eq.refl _, --or refl which is a type of eq.refl that infers or trivial which does some basic stuff
end

example : (exists (b : bool), b && tt = ff) → (∃ (b : bool), true) :=
begin
  assume h,
  cases h with w pf, --backing out the arguments we need to have our exists proof
  apply exists.intro w,
  trivial,
end

example : (∃ (b : bool), true) :=
begin
  --exact exists.intro tt true.intro,
  apply exists.intro tt,
  trivial,
end


/-
Let's set up some assumptions so that 
we can explore their consequences when
it comes to existentially quantified
propositions.
-/

/-
Beachballs! What could be more fun
-/

axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green
  (Red : Ball → Prop)     -- a Ball can be Red 
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red
  (b1g : Green b1)        -- b1 is green
  (b2r : Red b2)          -- b2 is red


example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume b,
  apply exists.elim b,  
  assume a b,
  apply exists.intro a b.left,
  --or you can use the following
  --cases b,
  --cases b_h,
  --apply exists.intro b_w,
  --exact b_h_left,
end 

example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume b,
  cases b,
  apply exists.intro b_w,
  apply or.symm b_h,
end 

example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h,
  apply exists.intro h_w,
  cases h_h,
  exact h_h,
  -- can't go further because this makes no sense aaaaaahhhhhh 
end 

example : 
    (∃ (b : Ball), Red b) → 
    (∃ (b : Ball), Red b ∨ Green b) := 
begin
  assume h,
  cases h,
  apply exists.intro h_w,
  exact or.intro_left _ h_h,
end 

/-
Social Networks
-/

axioms
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

example : 
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  assume e,
  cases h with p pf,
  apply exists.intro p,
  exact (pf e), -- exact pf works without the e because lean assumes 
end
#check Likes
/-
Write formal expressions for each of the following
English language sentences.
-/

-- Everyone likes him or herself
-- ∀ (p : People), Likes p p
-- Someone doesn't like him or herself
-- (∃ p : People), ¬ (Likes p p) or ¬∀ (p : People), Likes p p
-- There is someone who likes someone else
-- (∃ p1 p2 : People), Likes p1 p2
-- No one likes anyone who dislikes them

-- Everyone likes anyone who is nice

-- No one likes anyone who is not nice
-- ¬ (∃ p : Person),(∀ p2 : Person), ¬ nice p2 → likes p p2 

/-
If everyone who's nice likes someone, then
there is someone whom everyone who is nice 
likes.

((∀ p p2 : Person), (∃ p2 : Person) nice p → Likes p p2) → ((∃ p3 : Person), (∀ p4 : person), nice p4 → likes p4 p3 ) 

not true cause there can be many nice people who like different people
-/

example : ∃ n : ℕ, n = 1 :=
begin 
  exact exists.intro 1 (eq.refl 1), -- apply does not work here for some reason 
end


example : ¬ (∀ p : Person, Likes p p) ↔ ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _,

  --forwards
  assume a b,
  apply exists.elim a,
  assume c d,
  have e := b c,
  contradiction,
  --backwards
  assume a,
  have p := classical.em ∃ (p : Person), ¬Likes p p,
  cases p,
  -- one
  exact p,
  -- two
  have f : ∀ (p : Person), Likes p p := _, -- we will prove this later, the _ says we will assume true then prove later
  contradiction, 
  assume a,
  have aah := classical.em (Likes a a),
  cases aah,
  --one
  exact aah,
  --two
  have ah := exists.intro a aah,
  contradiction,


  --use sorry, ends goal but is no good for test - it is a skip to next question statement
  --sorry

end


 axiom triangle : Person → Person → Person → Prop
 axiom triangleDef : (∀ (p1 p2 p3 : Person), triangle p1 p2 p3 ↔ Likes p1 p2 ∧ Likes p2 p3 ∧ Likes p3 p1 )
