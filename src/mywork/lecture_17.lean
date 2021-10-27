import data.set

/-
We formally define two predicates on
natural numbers.

set theory is heavily ingrained in database software / design 

set theory is really just an application of what we have been doing so far

a set is just a predicate, a set of nats is just a predicate true for the nats in the set
-/
def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n


/-
We now formally represent some sets.
Bear in mind that we represent a set
as a predicate, applicable to a value
of the member type, and "reducing to"
a proposition, possibly "about" that
value.

In the following example, among other
things, we see that set ℕ and ℕ → Prop
are (nearly) interchangeable as types. 
A set is its defined by its membership
predicate. The "nearly" is because you
get to use set notations when you use
set T rather than T → Prop to specify
the type of a set value.


two ways to have a set

display notation:

def one_to_four : set ℕ := {1, 2, 3, 4}

or 

comprohention notation

def one_to_four : ℕ := {n : ℕ | _}

-/

def empte : set ℕ := { n : ℕ | false }

def complete : set ℕ := { n : ℕ | true }

def evens : set ℕ := { n : ℕ | ev n  }

def ods : set ℕ := { n : ℕ | od n } -- what if I want to have this be complete minus evens 

def evens_union_ods : set ℕ := { n : ℕ | (ev n) ∨ (od n) } -- this could also be true I think?

def evens_intersect_ods : set ℕ  := { n : ℕ | (ev n) ∧ (od n) } -- this could also be false I think

def evens_complement : set ℕ := { n : ℕ | ¬ ev n }

def ods_complement : set ℕ := { n : ℕ | ¬ od n }

def evens_intersect_empty : set ℕ := {n : ℕ | ev n ∧ false}

def evens_intersect_complete : set ℕ := {n : ℕ | ev n ∧ true}

def evens_union_empty : set ℕ := {n : ℕ | ev n ∨ false}

def evens_union_complete : set ℕ := {n : ℕ | ev n ∨ true}

-- fill in additional interesting combinations


/-
SET THEORY NOTATIONS
-/
/- empty set

Sometimes people use ∅ (phi) to represent the empty set
-/

#check ( ∅ : set ℕ )

/- set membership

A membership predicate applied to a value
yields a proposition: one that is true for
values in the set. The ∈ notation is just 
a shorthand for application of a membership
predicate to a value, but it gives a sense
of "inclusion" of a value in a collection
of values.
-/
#check evens 0
--^ same thing v
#check 0 ∈ evens
#check 1 ∈ evens

def od1 : set ℕ := complete \ evens
#check od1

def qiz := {n : ℕ | n < 5 ∧ n > 0}

def qiz2 := {n : ℕ | n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4}


/- set difference

Think of a set as a predicate. 

The difference between sets s1 and s2, 
written s1 \ s2, is the set of values
that are in s1 but not in s2. You can
think of this as the set s1 with the
elements in s2 "taken away." Sometimes
people use subtraction notation for
set difference: s1 - s2.
-/
#check evens \ ods
#check evens \ evens
#check evens \ empte
#check evens \ complete


/- complement

The complement of a set s is the set of all
values in the "universe of discourse" (in Lean,
a type) that are not in s. Lean doesn't provide
a notation, so we have to define it ourselves.
Here we define compl as the complement of a 
set of natural numbers.
-/

def compl_nat (s : set ℕ ) : set ℕ :=
{a | a ∉ s}
--∉ = not in 
#check compl_nat evens

/- union
The union of two sets, s1 and s2, written
as s1 ∪ s2, is the set of elements that are 
in s1 or s2. 
-/

#check ods ∪ complete
#check ods ∪ empte
#check ods ∪ evens


/- intersection 

The intersection of two sets, s1 and s2, written
as s1 ∩ s2, is the set of elements that are in s1
and in s2.
-/

#check ods ∩ empte
#check evens ∩ complete
#check ods ∩ evens

/- product 

The product of two sets, (s1 : set T) and
(s2 : set V) is the set of all pairs (t, v),
where t ∈ s1 and v ∈ t2. People sometimes
use × to represent the set product operation.
In Lean we have to define it ourselves.

all possible pairs - pair type

-/

def prodset {T V : Type} (s1 : set T) (s2 : set V) := 
  { pr : T × V | pr.1 ∈ s1 ∧ pr.2 ∈ s2 }

#check prodset evens empte
--^ turns into empty set
#check prodset evens ods 


/- subset

Given two sets, s1 and s2, of objects of some type 
T, we say that s1 is a subset of s2, written s1 ⊆ s2,
if every element in s1 is in s2. We say that s1 is a
proper subset of s2, written s1 ⊂ s2, if every value
in s1 is in s2 and some value in s2 is not in s1. 
-/

#check evens ⊆ evens
#check evens ⊂ evens
#check evens ⊆ complete
#check evens ⊂ complete
#check evens ⊂ empte
#check ∀ (s : set ℕ), empte ⊆ s


/- powerset

The powerset of a set, s, written 𝒫 s, is 
the set of all subsets of s. This makes the 
powerset a set of sets. 
-/

#check 𝒫 { 1, 2, 3}
#check 𝒫 evens


/-
Now let's state and prove some theorems.
-/


example : ∀ (n : ℕ), evens_union_ods n ↔ complete n := 
_


example : ∀ (n : ℕ), (n ∈ evens_union_ods) ↔ (n ∈ complete) := 
_


/-
Now we are in a position to see formal 
definitions of all of the preceding set
theory concepts.
-/

axioms (P Q : ℕ → Prop)

def pSet  : set nat := { n : ℕ | P n}
def qSet  : set nat := { n : ℕ | Q n}

#reduce 0 ∈ pSet
#reduce pSet ∪ qSet
#reduce pSet ∩ qSet
#reduce pSet \ qSet
#reduce pSet ⊆ qSet
#reduce 𝒫 pSet      -- harder to decipher


/-
Now that we understand these operations and
their corresponding notations in set theory,
we can start to state and prove theorems!
-/


