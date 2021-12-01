namespace implies 

/- axiom is the assumption we make with no proof 
If you want to prove p implies q, then assume p is true and then show q
-/

axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q



axiom p : P
-- assume P is true
-- assume we have a proof of p (p)

axiom pq : P → Q
-- we assume we have a proof pq of P → Q

-- intro for implies is assume premise, show conclusion 
-- elimination rule for implies: 
-- prop <-- P <---p hierarchy 
#check pq 
#check p
#check (pq p)

/- 
suppose P and Q are propositions and you
know that P → Q and that P are both true.
Show that Q is true

Proof: Apply the truth of P → Q to the truth
of P to derive the truth of Q. 

Proof: By the elimination rule for → with pq applied to p. 

Proof: By "modus ponens". QED (which was to be demonstrated)
-/
end implies
namespace all

/- Forall -/



axioms
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)
-- Does t have property P? YES because every object of type T have property p
example : P t := a t
-- proof a applied to t results in P being a property of t
#check a t
end all

/- AND & → -/

axioms (P Q : Prop)

/- Want a proof of P ∧ Q -/

