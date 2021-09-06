/-

To prove something for all types pick some arbitrary type
and then if it is true for the arbitrary type it will be true
for all types

-/

theorem eq_symm: 
  ∀ (T : Type) (x y : T), x = y → y = x := 
  begin 
    assume (T : Type), 
    assume (x y : T), 
    assume (e : x = y),
    rw e,
  end

/- English proof of the above statement:

When you are given x = y, substitutability allows you to replace any 
x with y and any y with x. Therefore substituting x for y and 
y for x you end up with y = x proving symmetry.

Theorem: Equality is symmetric. In orther words, 
∀ (T : Type) (x y : T), x = y → y = x. 

Proof: First we'll assume that T is any type and we have objects x and 
y of this type. What remains to be shown is that x = y → y = x. To
prove this, we'll assume the premise, x = y, and in this context we want 
to prove y = x. By the axiom of substitiutablilty  of equals, and using that fact
that x = y, we can rewrite as y = y which is true by the axiom of reflexivity. 
-/

theorem eq_trans:
  ∀ (T: Type) (x y z : T), x = y → y=z → x = z :=
    begin
      assume (T : Type),
      assume (x y z : T),
      assume (e1 : x = y), 
      assume (e2 : y = z),
      rw e1, --rewrites x = z to y = z with 
      exact e2,
    end

/- Weekend exercise: If i know x = y and y = z, prove that z = x 

-/