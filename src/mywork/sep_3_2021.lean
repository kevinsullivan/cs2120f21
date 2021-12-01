/- 
A Proof for equality being symetric
Theorem: equality is symetric 

To prove a forall assume big T is some type but never specify it. 

Lean info view is very helpful
-/

theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x := 
  begin 
    assume (T : Type), 
    assume (x y : T), 
    assume (e : x = y),
    rw e, 
  end 

/-
 An english / natural langauge proof for the above proof
Theorem: equality is symetric i.e ∀ (T : Type) (x y : T), x = y → y = x 

proof: Suppose there are two variables x and y of type T.
Assume x = y then by subsitution y = x. 

proof: First we'llassume that T is any type and we have objects x and y of this type
What remains to be shown is that x = y → y = x. to prove this, we'll assume x = y. 
By the axiom of subsitutability of equals. and using the fact x = y, we can rewrite
x in the goal as y, yielding y = y. This is true by the axiom of reflexivity of equality. 

QED (Latin abbreviation for quod erat demonstrandum: "Which was to be demonstrated." )

-/

theorem eq_trans: 
∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
begin 
  assume (T : Type),
  assume (x y z : T),
  assume (a : x = y),
  assume (b : y = z),
  rw a,
  exact b,
end

theorem eq_trans2: 
∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
begin 
  assume (T : Type),
  assume (x y z : T),
  assume (a : x = y),
  assume (b : y = z),
  rw a,
  rw b,
end 
/- this also works -/