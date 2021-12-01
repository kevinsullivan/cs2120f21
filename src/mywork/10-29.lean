def cong_mod (n a b : ℤ) : Prop :=
  ∃ k, a - b = k * n

#reduce cong_mod (4:ℤ)
#reduce cong_mod (4:ℤ) (6:ℤ) (10:ℤ) --evaluates to the proposition


example : cong_mod (4:ℤ) (6:ℤ) (14:ℤ) :=
begin
  unfold cong_mod,
  apply exists.intro (-2:ℤ) _,
  apply eq.refl,
end

--in functional programming, if we have a function that takes three arguments we can consider it a function that takes in one number and returns a function with two inputs and so on
-- this means we are partially evaluating the function by giving it the single number 4. 