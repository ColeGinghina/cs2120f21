import algebra.big_operators tactic.ring

/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.

1: Write the principle of complete induction using the notation of symbolic logic.

Principle of Complete Induction. Let P be any property that satisfies 
the following: for any natural number n, whenever P holds of every number 
less than n, it also holds of n. Then P holds of every natural number.

∀ (n : ℕ), ∀ (a : ℕ) (P : n a → Prop), (a < n ∧ P a) → P n

#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 

2: Show that for every n, 0^2 + 1^2 + 2^2 + … n^2 = (1/6)n(1+n)(1+2n).

First, we must prove that this statement is true for n = 0. To do this, we must
prove the statement 0^2 = (1/6)(0)(1+0)(1+2(0)). This can be simplified to
0 = (1/6)(0)(1)(1) using algebra. Because 0 is an absorbing number in multiplication,
the right side of the equation simplifies to 0, showing that the propisition is true
for n = 0. Then, we must show that the statement holds true for n' and its successor, n' + 1.
First, we assume n' and (n' + 1) as well as the induction hypothesis 
that P(n') = (1/6)(n')(1 + n')(1 + 2n'). We then need to show P(n' + 1), which can
be written as (1/6)(n' + 1)(1 + (n' + 1))(1 + 2(n' + 1)). This can be simplified to be
P(n' + 1) = (1/6)(n' + 1)(n' + 2)(2n' + 3). Using our induction hypothesis, we can rewrite
P(n' + 1) as (1/6)(n')(1 + n')(1 + 2n') + (n + 1)^2 as P(n') is the sum of all terms
up to n = n'. We must then show that (1/6)(n')(1 + n')(1 + 2n') + (n' + 1)^2 equals
(1/6)(n' + 1)(n' + 2)(2n' + 3) through algebra. We first multiply (n' + 1)^2 by 6/6
to get equivalent denominators. We then expand 6(n' + 1)^2 and then factor out (n' + 1),
leaving us with the expression (1/6)(n' + 1)(n'(2n' + 1) + 6(n' + 1)). Distributing the
n' and 6, then adding the appropriate terms together leaves us with the expression
(1/6)(n' + 1)(2n'^2 + 7n' + 6). This can be factored to read (1/6)(n' + 1)(n' + 2)(2n' + 3),
which is equivalent to our induction step of P(n' + 1). This algebra proves that for
any n value, the proposition is true for its successor, n + 1. ∀ n, P n.

-/

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/

def sum_of_squares : ℕ → ℕ
| 0 := 0
| (nat.succ n) := (sum_of_squares n) + (n.succ * n.succ)

#eval sum_of_squares 4
#eval sum_of_squares 5

def P : ℕ → Prop := λ n, 6 * sum_of_squares (n) = n * (n + 1) * ((2 * n) + 1)

theorem conjecture : ∀ n, P n :=
begin
    assume n,
    unfold P,
    induction n with n' ih_n',
    refl,
    simp [sum_of_squares],
    rw [mul_add, ih_n', nat.succ_eq_add_one],
    ring,
end

--10

/-
Give an informal but detailed proof that for every natural number 
n, 1⋅n=n, using a proof by induction, the definition of multiplication, 
and the theorems proved in Section 17.4.
-/

/-
First, we must show that the statement P(n) = ∀ (n : ℕ), 1 * n = n is true at a value of
n = 0 as a base case. Using simple algebra, we can prove that 1 * 0 = 0, as
0 is an absorbing number in multiplication. We then must show that this statement
is true for any n' and its successor n' + 1. To do this, we first assume the 
induction hypothesis of P(n') = 1 * n' = n'. We must then show the induction step, 
which is P(n' + 1) = 1 * (n' + 1) = n' + 1. Using the definition of multiplication, 
we can rewrite this to be P(n' + 1) = 1 * n' + 1, as n' + 1 is equivalent to
the successor of n'. Using simple algebra, we can equate 1 * n' + 1 to n' + 1, 
proving that the statement 1 * n = n is true for both n' and n' + 1.
-/

-- 11

/-
Show that multiplication distributes over addition. In other words, 
prove that for natural numbers m, n, and k, m(n+k)=mn+mk. You should 
use the definitions of addition and multiplication and facts proved 
in Section 17.4 (but nothing more).
-/

/-
To prove the proposition P(m) = ∀ (m n k : ℕ), (m * (n + k)) = (m * n) + (m * k), 
we will perform induction on m and fix the values of n and k. First, 
we must show that this proposition holds true for a value of m = 0 as a base case. 
This leaves us with P(0) = (0 * (n + k)) = (0 * n) + (0 * k). Using simple algebra,
we can see that both sides of this equation equate to 0, showing that it is 
true at a value of m = 0. We must then show that the statement is true for both
m' and its successor m' + 1. We assume both these values and the induction hypothesis
of P(m') = (m' * (n + k)) = (m' * n) + (m' * k). We must then show the induction step of
P(m' + 1) = ((m' + 1) * (n + k)) = ((m' + 1) * n) + ((m' + 1) * k). First, using the
definition of multiplication, we can rewrite (m' + 1) * (n + k) as
(n + k) * m' + (n + k), as m' + 1 is equivalent to the successor of m'. Using our
induction hypothesis, we can then distribute m' to get a statement of
(m' * n) + (m' * k) + (n + k). Using the commutivity and associativity principles of
addition, we can rewrite that statement to read (m' * n) + n + (m' * k) + k. Through
the defintion of multiplication in terms of addition, we can then rewrite the terms
(m' * n) + n and (m' * k) + k as ((m' + 1) * n) and ((m' + 1) * k) respectively. This
is because m' + 1 is the successor of m', and the definition of multiplication reads
succ(m) + n = m * n + n. We now have the proposition of ((m' + 1) * n) + ((m' + 1) * k),
which is equiavlent to our induction step and shows that P(m') → P(m' + 1), proving
the proposition true for all natural numbers.
-/

-- 12

/-
Prove the multiplication is associative, in the same way. 
You can use any of the facts proved in Section 17.4 and the previous exercise.
-/

/-
In this proof, we will write the proposition that multiplication is associative as P(k) =
∀ (m n k : ℕ), (m * (n * k)) = ((m * n) * k). To prove this, we will fix m and n 
and perform induction on k. First, we must prove this true at a base case of 
k = 0. To do this, we plug in 0 at k to get (m * (n * 0)) = ((m * n) * 0). Because
0 is an absorbing number in multiplication, we can use simple algebra to determine that
both sides equal 0, showing that the proposition is true for P(0).  We must then show
that the statement is true for some value, k', and its successor k' + 1. We assume both
these values and the induction hypothesis that P(k') = (m * (n * k')) = ((m * n) * k').
We then must prove P(k' + 1) = (m * (n * (k' + 1))) = ((m * n) * (k' + 1)). First, we
can use the definition of multiplication to write ((m * n) * (k' + 1)) as 
((m * n) * k') + (m * n), as k' + 1 is the successor of k'. Then, using our induction
hypothesis, we can rewrite the left term as (m * (n * k')) to get (m * (n * k')) + (m * n).
We can then factor out the term m from both sides of the + using our previous proof
that multiplication distributes over addition. This leaves us with
m * ((n * k') + n). Using the definition of multiplication once again, we can rewrite
(n * k') + n as n * (k' + 1). This gives us m * (n * (k' + 1)), which is equivalent to our
induction step. This shows that P(k') → P(k' + 1), therefore proving the proposition by
induction.
-/

--13

/-
Prove that multiplication is commutative.
-/

/-
In this proof, we will write the proposition that multiplication is commutative as
P(n) = ∀ (m n : ℕ), (m * n) = (n * m). To prove this, we will fix m and perform 
induction on n. First, we must prove this statemen true for the base case of n = 0. By plugging 
in 0 for n, we are left with m * 0 = 0 * m. Using simple algebra, we can determine both sides
to be 0, therefore proving P(0) to be true. We must then show that the statement is true
for some vale, n', and its successor n' + 1. We assume both these values and the induction
hypothesis of P(n') = m * n' = n' * m. We must then prove the induction step,
P(n' + 1) = m * (n' + 1) = (n' + 1) * m. Using the defintion of multiplication, we can 
rewrite m * (n' + 1) as m * n' + m, as n' + 1 is the successor of n'. Using the principle
that addition is commutative, we can then rewrite this statement as m + (m * n'). Using our
induction hypothesis, we see m * n' = n' * m, so we can rewite m * n' as n' * m. This gives
us m + (n' * m). Using the principle of commutivity on addition, we can rewrite this as 
(n' * m) + m. Then, using the definition of multiplication, we can rewrite the statement
as (n' + 1) * m, giving us an equivalent statement to our induction step. This shows that
P(n') → P(n' + 1), therefore proving the proposition by induction.
-/