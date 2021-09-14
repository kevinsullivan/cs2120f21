namespace implies

axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q -- how to write an if then statement in lean

/-
To prove the above prop assume that P is true and prove that
in the context of that assumption Q is true
-/

axiom p : P
--assume p is true
--assume we  have  a proof of P (p)

axiom pq : P → Q
axiom PQ : if_P_is_true_then_so_is_Q
--assume we have a proof, pq, of P → Q

--introduction rule for implies: assume premise, show coclusion

--elimination rule for implies: use the implies relation along with
--a proof that P is true to prove Q is true

#check pq
#check p
#check (pq p)

/-
Suppose P and Q are propositions and you know that P → Q and that P are both true.
Show that Q is true.

Proof : Apply the truth of P → Q to the truth of p to derive the truth of Q.

Proof: By the elimination rule for → with pq applied to p.begin
  
Proof: By "modus ponens". QED
-/
end implies

namespace all

/-
FORALL
-/

axioms
  (T:Type)
  (P : T → Type)
  (t: T)
  (a : ∀ (x: T), P x)

-- Does t ahve property P

example : P t := a t

#check a t
s

end all 

