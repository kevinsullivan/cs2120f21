import algebra.algebra.basic tactic.ring 

namespace hidden

--data types are often defined inductively?
--some notion of looping, that we can build and build

inductive nat : Type  --defining a new type in lean uses the keyword inductive
| zero : nat
| succ (n' : nat) : nat

def z := nat.zero
def o := nat.succ nat.zero
def t := nat.succ (nat.succ nat.zero)


#reduce z
#reduce o
#reduce t

def f : nat :=
begin
  exact nat.succ (nat.succ t)
end

def inc : nat → nat := 
begin
  assume n,
  exact nat.succ n,
end 

def inc' : nat → nat 
| n := nat.succ n

def dec : nat → nat --all functions in lean must be total 
| (nat.zero) := nat.zero
| (nat.succ n ) := n -- we need these parenthesies for some reason 
--pattern matching as a construct is super useful -- kinda like lambda functions? 

def add : nat → nat → nat 
| (nat.zero) (n) := n 
| (nat.succ n) (m) := nat.succ (add n m)
--this is function defenition form  

#reduce inc f
#reduce add o t

def mul : nat → nat → nat 
| (nat.zero) (n) := nat.zero 
| (nat.succ n) (m) := add (mul n m) m

#reduce mul t f --it works!

def exp : nat → nat → nat
| (m) (nat.zero) := (nat.succ nat.zero)
| (m) (nat.succ n) := mul (exp m n) m

#reduce exp t o
#reduce exp o t
#reduce exp t t

def sum_to : nat → nat 
| (nat.zero) := (nat.zero)
| (nat.succ n) := add (nat.succ n) (sum_to n)

#reduce sum_to t


theorem foo : ∀ (n : nat), P n :=

end hidden

def P : nat → Prop 
| n := 2 * sum_to n = n * (n + 1)

--recursive data structures are best proven with induction