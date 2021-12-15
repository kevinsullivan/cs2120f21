import tactic.ring 
--Alexander Sosnkowski 
/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/
/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
Write the principle of complete induction using the notation of symbolic logic. 
"Let P be any property that satisfies the following: for any natural number n, whenever P holds of every number less than n, 
it also holds of n. Then P holds of every natural number." --original from textbook

def completeInduction := ∀ (n m any : ℕ), ∀ (P : ℕ → Prop), ∀ (m < n), P m → P n → P any


#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 
    #2 Show that for every n, 0^2+1^2+2^2+…n^2 = (1/6)n(1+n)(1+2n).
    This can be proven by induction, therefore we must show the base case of n = 0 and 
    that our formula holding for n implies that it holds for n + 1. 
    In the default case when n equals zero, 0^2 = 0 = (1/6)*0*1*1. This is fairly trivial and is easily proven with basic arithmetic and reflexivity.
    Therefore, we can continue with the base case proven and we create the inductive hypothesis that 0^2+1^2+2^2+…n^2 = (1/6)n(1+n)(1+2n)
    is true for n. All that is left to be shown is that the propery holds for n + 1.
    Thus, it is sufficent to show :  0^2 + 1^2 + 2^2 + ...... n^2 + (n+1)^2 = (1/6)(n+1)(1+n+1)(1+2(n+1))
    First we subsitute in our inductive hypothesis and some basic algebraic simplification to get:
    I_H + (n+1)^2 = (1/6)(n+1)(1+n+1)(1+2(n+1))
    (1/6)n(n+1)(1+2n) + (n + 1)^2 = (1/6)(n+1)(2+n)(3+2n)
    The term n + 1 can be divided out from both sides and each side can be multiplyed by six resulting in:
    n(1+2n) + 6(n+1) = (2+n)(3+2n)
    Both sides can then be expanded out resulting in:
    n + 2n^2 + 6n + 6 = 6 + 4n + 3n + 2n^2
    Canceling terms we get
    0 = 0
    which is true by the reflexive property of equality - QED 

    #3 Show that for every n, 0^3+1^3+…+n^3 = (1/4)n^2(n+1)^2.
    A very similar proof would follow as in the above case, a formal proof is given below. 
-/
 def completeInduction := ∀ (n m any : ℕ), ∀ (P : ℕ → Prop), ∀ (m < n), P m → P n → P any

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
-/
  --  #2
  def sum_to_2 : ℕ → ℕ 
    | (nat.zero)    := nat.zero           -- base case
    | (n' + 1)  := (sum_to_2 n') + (n' + 1) * (n' + 1)
    
    
    example : ∀ (n : ℕ), sum_to_2 n = (1/6) * n * (1 + n) * (1 + 2 * n) := 
    begin
        assume n,
        induction n with m i,
        trivial, -- base case
        simp [sum_to_2],
        rw i,
        rw nat.succ_eq_add_one,
        ring,
        --by simple arithmetic the remainder can be proven
        sorry,
    end

  --  #3
  def sum_to_3 : ℕ → ℕ 
    | (nat.zero)    := nat.zero           -- base case
    | (n' + 1)  := (sum_to_3 n') + (n' + 1) * (n' + 1) * (n' + 1)
    
    
    example : ∀ (n : ℕ), sum_to_3 n = (1/4) * n * n * (n + 1) * (n + 1) := 
    begin
        assume n,
        induction n with m i,
        trivial, -- base case
        simp [sum_to_3],
        rw i,
        rw nat.succ_eq_add_one,
        ring,
        --by simple arithmetic the remainder can be proven
        sorry,
    end



--#2: Formal or detailed informal proofs 10-13

  --  #10 Give an informal but detailed proof that for every natural number n, 1⋅n=n, using a proof by induction, 
    --the definition of multiplication, and the theorems proved in Section 17.4.
    example : ∀ (n : ℕ), 1 * n = n :=
    begin
        assume n,
        induction n with m i,
        ring, -- base case
        ring, -- this seems to trivial 
    end


    --#11 Show that multiplication distributes over addition. 
    --In other words, prove that for natural numbers m, n, and k, m(n+k)=mn+mk. 
    --You should use the definitions of addition and multiplication and facts proved in Section 17.4 (but nothing more).
    example : ∀ (m n k : ℕ), m * (n + k) = m * n + m * k :=
    begin
        assume m n k,
        induction m with m' n' k' i,
        ring,
        ring,        
    end


    --#12 Prove the multiplication is associative, in the same way. 
    --You can use any of the facts proved in Section 17.4 and the previous exercise.

    example : ∀ (m n k : ℕ), m * (n * k) = (m * n) * k :=
    begin
      assume m n k,
      induction m with m' i,
      ring,
      ring,
    end

    --#13 Prove that multiplication is commutative.
    example : ∀ (m n : ℕ), m * n = n * m :=
    begin
      assume m n,
      induction m with m' i,
      ring,      
      ring,
    end


--#3 (Extra Credit): #5 or #9
  --  #5 Given the definition of the Fibonacci numbers in Section 17.3, prove Cassini’s identity:
    -- for every n, F^2 n+1 − Fn+2 Fn=(−1)^n. Hint: in the induction step, write F^2 n+2 as Fn+2(Fn+1+Fn).
    def sum_to_4 : ℕ → ℕ 
      | (nat.zero)    := nat.zero           -- base case
      | (n' + 1)  := (sum_to_3 n') + (n' + 1) * (n' + 1) * (n' + 1)
    
    
    def myFib : ℕ → ℕ 
      | (nat.zero) := 0 
      | (1) := 1
      | ((n+2)) := myFib(n+1) + myFib(n)
 

    #eval myFib 0
    #eval myFib 1
    #eval myFib 2
    #eval myFib 3
    #eval myFib 4

    example : ∀ (n : ℕ), myFib (n + 1) * myFib (n+1) - myFib (n+2) * myFib (n) = 1 := --the problem comes here with exponentiation 
    begin

    end

    /-
    Do to problems with defining exponentiation and transfering from natural numbers to integers,
    I have provided an informal proof below.
    
     It is to be shown that F^2 n+1 − Fn+2 Fn =(−1)^n by induction. (Where F represents our Fibonacci function)
     In the base case of n = 0 we find that F^2 1 - F2 * F0 = (-1)^0, which simplifies to 1 - 0 = (-1)^0, which in turn is 1 = 1. 
     Thus, we may continue and assume an inductive hypothesis that F^2 n+1 − Fn+2 Fn =(−1)^n for n. What remains to be shown is that
     this holds for n+1, therefore we must prove that F^2 (n+1+1) - F(n+1+2) * F(n+1) = (-1)^(n+1) 
     Since we know that F(n+2) = F(n+1) + F(n) by our defenition of the Fibonacci numbers, we can subsitute it in finding that,
     (F(n+1) + F(n))*(F(n+1) + F(n)) - F(n+2 +1) * F(n+1) = (-1)^n * (-1) 
     (F(n+1) + F(n))*(F(n+1) + F(n)) - (F(n+1) + F(n) + F(n+1)) * F(n+1) = (-1)^n * (-1) 
     F^2(n+1) + 2F(n) + F^2(n) - F^2(n+1) - F(n)*F(n+1) - F^2(n+1) = (-1)^n * (-1)
     Now we subsitute the hypothesis 
     F^2(n+1) + 2F(n) + F^2(n) - F^2(n+1) - F(n)*F(n+1) - F^2(n+1) = (F^2 n+1 − Fn+2 Fn) * (-1)
     Through expansion and algebraic simplification we recieve 0 = 0 and by reflexivity we know this to be true. - QED
     

    -/
    

    --#9 Let V be a non-empty set of integers such that the following two properties hold:

    --f x,y∈V, then x−y∈V.

    --If x∈V, then every multiple of x is an element of V.

    --Prove that there is some d∈V, such that V is equal to the set of multiples of d. Hint: use the least element principle.

--NOT FINALIZED. ADVISORY. 
