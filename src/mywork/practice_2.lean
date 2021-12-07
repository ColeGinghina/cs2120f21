/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _  -- trick question? why?

/-
There is no proof of false because if there were,
then false would be true.
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume h,
      exact h,
    -- right disjunct is true
      assume h,
      exact h,
  -- backward
    assume p,
    apply or.intro_left P p,
end

/-
First you assume P, the only proposition in the example.
You then apply the introduction rule to iff to prove both sides
of the proposition. You then assume P ∨ P to be true using the intro
rule for implies. Using the elimation rule for or, you then need to prove
that both sides of P ∨ P imply P, which is done so by assuming P and then 
exacting that assumption. To prove the example backwards we assume P and
then exact it to either side of the or statement to prove it true.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pandp,
  apply and.elim_left pandp,
  assume p,
  apply and.intro p p,
end

/-
We first assume P and then apply the introduction rule for iff. To prove
it forwards, we use the intro rule for implies and assume P ∧ P. By applying
the elimination rule to either side of this assumption we get a proof of P, 
which proves the example forwards. To prove it backwards, we assume a proof
of P through the intro rule for implies. We then the intro rule for and to
P ∧ P, both sides of which are proven through exacting the assumed proof of P.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume porq,
  apply or.elim porq,
    assume p,
    apply or.intro_right Q p,
    assume q,
    apply or.intro_left P q,
  assume qp,
  apply or.elim qp,
    assume q,
    apply or.intro_right P q,
    assume p,
    apply or.intro_left Q p,
end

/-
First we assume P and Q and apply the intro rule for iff. We then assume
P ∨ Q using the intro rule for implies and apply the elimination rule for
or to it. To prove P → Q ∨ P, we assume P and then apply the intro rule for or 
to the right of Q ∨ P. To prove Q → Q ∨ P, we assume Q and then apply the
intro rule for or to the left or Q ∨ P. To prove the statement backwards, we
first assume a proof of Q ∨ P. We repeat all the above steps, using first
the elimination rule for or then assuming a proof for the given proposition
and applying the intro rule for or to the appropriate side.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pandq,
  apply and.intro _ _,
    apply and.elim_right pandq,
    apply and.elim_left pandq,
  assume qandp,
  apply and.intro _ _,
    apply and.elim_right qandp,
    apply and.elim_left qandp,
end

/-
First we assume P and Q and apply the intro rule for iff. To prove
ir forwards, we assume P ∧ Q through the intro rule for implies.
We then apply the intro rule for and to prove both Q and P. By applying
the elimination rule for and to the right we get a proof of Q, and the
elimination rule to the left for and we get a proof of P. To prove the
statement backwards, we assume Q ∧ P through the intro rule for implies.
We then apply the intro rule for and to isolate Q and P. We then apply
the elimination rule for and to the right to get a proof of P, and the 
elimination rule for and to the left to get a proof of Q.
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : (Q ∨ R) := and.elim_right pqr,
  apply or.elim qr,
  assume q,
  apply or.intro_left _,
  apply and.intro p q,
  assume r,
  apply or.intro_right _,
  apply and.intro p r,
  -- backwards
  assume pqr,
  apply and.intro _ _,
  apply or.elim pqr,
  assume pq,
  apply and.elim_left pq,
  assume pr,
  apply and.elim_left pr,
  apply or.elim pqr,
  assume pq,
  apply or.intro_left _,
  apply and.elim_right pq,
  assume pr,
  apply or.intro_right _,
  apply and.elim_right pr,
end

/-
We first assume P Q and R and apply the intro rule for iff. To 
prove the statement forward we assume P ∧ (Q ∨ R) through the intro
rule for implies. We can then assume both sides of the and statement
to be true, labeling the proof of P as p and the proof of Q ∨ R as
qr. By applying the elimination rule for or to qr, we get the statements
that both Q and R individually prove (P ∧ Q) ∨ (P ∧ R). We first assume 
Q to be true through the intro rule for implies, we we can pair with
our existing proof of P through the introduction rule for and to prove
the left side of (P ∧ Q) ∨ (P ∧ R). This proves the whole statement through
the left version of the intro rule for or. We then repeat this process with 
an assumption of R through the intro rule for implies, instead proving the
right side of the statement through the intro rule for or. To prove the
example backwards, we first assume (P ∧ Q) ∨ (P ∧ R) through the intro
rule for implies, which we will call pqr. We then apply the intro rule for and
to break up the two sides of P ∧ (Q ∨ R). We then apply the elimination rule
for or to pqr to show that both P ∧ Q and P ∧ R imply P. Because both statements
contain P, by first assuming them to be true through the intro rule for
implies we can then insitute the correct side of the elimination rule for 
and to get a proof of P. To prove Q ∨ R, we once again apply the intro rule
for or. We assume P ∧ Q and P ∧ R to be true in each case respectively through
the intro rule for implies. We can then apply the intro rule for or to Q ∨ R
to whichever side applies to either ∧ statment. We then apply the elimination
rule for and to either the Q side or R side of the ∧ statements, proving the
entire example.
-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forwards
  assume pqr,
  apply and.intro _ _,
  apply or.elim pqr,
  assume p,
  apply or.intro_left _,
  exact p,
  assume qr,
  apply or.intro_right _,
  apply and.elim_left qr,
  apply or.elim pqr,
  assume p,
  apply or.intro_left _,
  exact p,
  assume qr,
  apply or.intro_right _,
  apply and.elim_right qr,
  -- backwards
  assume por,
  have porq : (P ∨ Q) := and.elim_left por,
  have porr : (P ∨ R) := and.elim_right por,
  apply or.elim porq,
  assume p,
  apply or.intro_left _,
  exact p,
  assume q,
  apply or.elim porr,
  assume p,
  apply or.intro_left _,
  exact p,
  assume r,
  apply or.intro_right _,
  apply and.intro q r,
end

/-
We first assume P Q and R and apply the intro rule for iff. We then
assume P ∨ (Q ∧ R) through the intro rule for implies which we will call
pqr. Apply the intro rule for and we are left to prove P ∨ Q and P ∨ R. 
Applying the elimination rule for or to pqr, we are left to prove that P
impies P ∨ Q and Q ∧ R implies P ∨ Q. We first assume we have a proof of P
through the intro rule for implies, which we can apply to the left side of
P ∨ Q through the intro rule for or to prove the statement. We can then assume
Q ∧ R implies P ∨ Q through the intro rule for implies. Applying the right side
of the intro rule for or to P ∨ Q, we are left needing a proof of Q which we
get by applying the right side of the elimination rule for and to Q ∧ R. We can
then repeat this whole process, starting with applying the elimination rule for
or to pqr to prove P ∨ R, instead using the R side of Q ∧ R through the elimination
rule for and. To prove it backwards we first assume a proof of (P ∨ Q) ∧ (P ∨ R)
through the intro rule for implies. We can then obtain proofs for both
P ∨ Q and P ∨ R through the elimination rules for and. By then applying the
elimination rule for or to P ∨ Q, we can assume a proof of P through the
intro rule for implies, which can be applied to the left side of P ∨ (Q ∧ R)
through the intro rule for or to prove it true. We can thrn assume a proof
of Q through the intro rule for implies, followed by an application of the
elimination rule for or to P ∨ R. We can then once again assume a proof of P
through the intro rule for implies and apply it to the left side of P ∨ (Q ∧ R).
We can then assume a proof of R through the intro rule for implies, meaning
we then have a proof of both Q and R. We can apply these proofs to the right
side of P ∨ (Q ∧ R) through the right side of the intro rule for or, connecting
them with the intro rule for and.
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume ppq,
  apply and.elim_left ppq,
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left _,
  exact p,
end

/-
We first assume P and Q and apply the intro rule for iff. We can then assume
P ∧ (P ∨ Q) through the intro rule for implies. Applying the elimination rule
for and to the left side of P ∧ (P ∨ Q), we get a proof of P and prove the
statement forwards. To prove it backwards, we first assume a proof of P
through the intro rule for implies. Applying the intro rule for and we then
have to prove both P and P ∨ Q. By exacting our proof of P we prove P. Then
using the intro rule for or to the left and exacting the proof of P again
we prove P ∨ Q.
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume ppq,
  apply or.elim ppq,
  assume p,
  exact p,
  assume pq,
  apply and.elim_left pq,
  assume p,
  apply or.intro_left _,
  exact p,
end

/-
We first assume P and Q and apply the intro rule for iff. We then assume
P ∨ (P ∧ Q) using the intro rule for implies. Applying the elimination rule
for or to P ∨ (P ∧ Q) we then have to prove P → P and P ∧ Q → P. We can assume
the precendent in both cases through the intro rule for implies. In the first
case we exact the proof of P to prove P. In the second case we can use the 
elimination rule for and to the left to get a proof of P. To prove it backwards,
we first assume a proof of P through the intro rule for implies. Using the intro
rule for or to the left we are lefting needing to prove P. We exact our proof
and finish the example.
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  assume ptrue,
  apply true.intro,
  assume t,
  apply or.intro_right _,
  apply true.intro,
end

/-
We first assume P and apply the intro rule for iff. We assume P ∨ true
using the intro rule for implies, which proves true to be true through the
intro rule for true which states that true is always true. To prove it backwards
we assume true to be true, and then use the intro rule for true to prove
P ∨ true to be true using the intro rule for or on the right side.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pfalse,
  cases pfalse,
  exact pfalse,
  cases pfalse,
  assume p,
  apply or.intro_left _,
  exact p,
end

/-
We first assume P and apply the intro rule for iff. We then assume
P ∨ false to be true using the intro rule for implie. We then institute a
case analysis on P ∨ false, which reveals that false is never true. Therefore,
P must be true for the or statement to be true. We exact P ∨ false as a proof of
P. We then do another case analysis that shows that false cannot prove P. To
prove it backwards we first assume we have a proof of P using the intro rule
for implies. We apply the intro rule for or to the left side of P ∨ false and
exact our proof of P to prove the statement true.
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume ptrue,
  apply and.elim_left ptrue,
  assume p,
  apply and.intro _ _,
  exact p,
  apply true.intro,
end

/-
We first assume P and apply the intro rule for iff. We then assume
P ∧ true using the intro rule for implies. Using the left side of
the elimination rule for and we get a proof of P which can be applied to prove
the example forwards. To prove it backwards we first assume we have a proof
of P using the intro rule for implies. We apply the intro rule for and to
isolate both side of P ∧ true. We first prove P using our assumption and then
prove true using the intro rule for true.
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  assume pfalse,
  have f : false := and.elim_right pfalse,
  exact f,
  assume f,
  apply and.intro _ _,
  cases f,
  exact f,
end

/-
We first assume P and apply the intro rule for iff. We then assume
P ∧ false using the intro rule for implies. We can using the elimination
rule for and on the right side to get a proof of false, which can be exacted
to prove false. To prove it backwards, we assume false using the intro
rule for implies. We then use the intro rule to isolate P and false. We then
use case analysis on our assumption of false to show that it cannot prove P,
making the statement false. We then exact our proof of false to show that false
is false, making the statement P ∧ false imply false.
-/