import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
If there's a function that maps/takes every α value 
and implies β, then for all objects a of type α, when
predicate p is applied to a this implies predicate q
applied to function f with passing value a. In turn, this
implies the existence of a value a of type α such that when
predicate p is applied to a there is an implication that
there exists a value b of type β such that predicate q
is applied to b.
-/


-- Give your formal proof here

begin
  intros one two,
  cases one with w pf,  
  cases two with w2 pf2,
  apply exists.intro (w w2),
  exact (pf w2 pf2),
end


/-
First, introduce the two implications. The first is
the existence of a function f that when applied to
α implies β, and for all values alpha, prop p applied to alpha
implies prop q applied to function f with alpha. The second
is the existence of a value of alpha that has the prop
p applied to it. By doing case analysis on both these
assumptions, we get a witness and a predicate for 
each statement. For the first, this is a proof of
α → β and of the aforementioned for all statement.
For the second, this is a proof of α and prop p
applied to that value of α. By applying the value α to 
the witness α → β, we get a value β and can use this value
to apply exists.intro to the statement we are trying to prove.
Afterwards, we only need to prove prop q applied to witness 1
and witness 2. By exacting w2 applied to the first predicate,
followed by the second predicate, we are given a proof of
q (w1 w2), which accomplishes all goals.
-/