axioms 
  (Person : Type)
  (Likes : Person → Person → Prop) --binary relation on objects of type person

example : ¬ (∀ p : Person, Likes p p) ↔ ∃ p : Person, ¬ Likes p p:= --still true if ∀ set is empty
begin
  apply iff.intro,
  --forward
  assume h,
  have f := classical.em (∃ p : Person, ¬ Likes p p),
  cases f,
    --case 1
    assumption,
    --case 2
    have contra : ∀ (p : Person), Likes p p:= _,
    contradiction,
    assume p,
    have g := classical.em (Likes p p),
    cases g,
    exact g,
    have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
    contradiction,
  --backward 
  assume h,
  
  
end