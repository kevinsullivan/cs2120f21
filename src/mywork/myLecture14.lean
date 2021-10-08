-- 14

axioms
  (Person : Type)
  (Likes: Person → Person → Prop) --binary operation, two place predicate 

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=

  begin 
    apply iff.intro _ _,
    --forward
    assume P,    
    have f := classical.em ( ∃ (p : Person), ¬Likes p p),
    cases f,
    --one
    assumption,
    --two
    have contra : ∀ (p : Person), Likes p p := _,
    contradiction,
    assume p,
    have t := classical.em (Likes p p),
    cases t,
    --one
    assumption,
    --two
    have f2 := exists.intro p t,
    contradiction,
    --backwards
    assume P,
    assume a,
    apply exists.elim P,
    assume b c,
    have f := a b,
    contradiction,
  end 