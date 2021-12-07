/-
ctg8h@virginia.edu, https://github.com/ColeGinghina/cs2120f21.git
-/

-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume npq,
  apply or.elim (em P),
  assume p,
  apply or.intro_right _,
  assume q,
  have pq : P ∧ Q := and.intro p q,
  apply npq pq,
  assume np,
  apply or.intro_left _,
  exact np,
  assume pq,
  assume pandq,
  have p := pandq.left,
  have q := pandq.right,
  apply or.elim pq,
  assume np,
  apply np p,
  assume nq,
  apply nq q,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume npq,
  apply and.intro _ _,
  apply or.elim (em P),
  assume p,
  assume p,
  have porq : P ∨ Q,
  apply or.intro_left,
  exact p,
  apply npq porq,
  assume np,
  exact np,
  apply or.elim (em Q),
  assume q,
  assume q,
  have porq : P ∨ Q,
  apply or.intro_right,
  exact q,
  apply npq porq,
  assume nq,
  exact nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume porpq,
  apply or.elim (em P),
  assume p,
  apply or.intro_left _,
  exact p,
  assume np,
  cases porpq,
  apply or.intro_left _,
  exact porpq,
  have q := porpq.right,
  apply or.intro_right,
  exact q,
  assume porq,
  apply or.elim porq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim (em P),
  assume p,
  apply or.intro_left,
  exact p,
  assume np,
  apply or.intro_right,
  apply and.intro np q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqpr,
  have porq := pqpr.left,
  have porr := pqpr.right,
  apply or.elim porq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim porr,
  assume p,
  apply or.intro_left,
  exact p,
  assume r,
  apply or.intro_right,
  exact and.intro q r,
  assume pqr,
  apply and.intro _ _,
  apply or.elim pqr,
  assume p,
  apply or.intro_left,
  exact p,
  assume qr,
  have q := qr.left,
  apply or.intro_right,
  exact q,
  apply or.elim pqr,
  assume p,
  apply or.intro_left,
  exact p,
  assume qr,
  have r := qr.right,
  apply or.intro_right,
  exact r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  assume pqrs,
  have porq := pqrs.left,
  have rors := pqrs.right,
  apply or.elim porq,
  assume p,
  apply or.elim rors,
  assume r,
  apply or.intro_left,
  exact and.intro p r,
  assume s,
  apply or.intro_right,
  apply or.intro_left,
  exact and.intro p s,
  assume q,
  apply or.elim rors,
  assume r,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  exact and.intro q r,
  assume s,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  exact and.intro q s,
  assume ors,
  apply and.intro _ _,
  apply or.elim ors,
  assume pandr,
  apply or.intro_left,
  apply and.elim_left pandr,
  assume ors2,
  apply or.elim ors2,
  assume pands,
  apply or.intro_left,
  apply and.elim_left pands,
  assume ors3,
  apply or.elim ors3,
  assume qandr,
  apply or.intro_right,
  apply and.elim_left qandr,
  assume qands,
  apply or.intro_right,
  apply and.elim_left qands,
  apply or.elim ors,
  assume pandr,
  apply or.intro_left,
  apply and.elim_right pandr,
  assume ors2,
  apply or.elim ors2,
  assume pands,
  apply or.intro_right,
  apply and.elim_right pands,
  assume ors3,
  apply or.elim ors3,
  assume qandr,
  apply or.intro_left,
  apply and.elim_right qandr,
  assume qands,
  apply or.intro_right,
  apply and.elim_right qands,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n : ℕ), n ≠ 0  := 
begin
  apply exists.intro 1,
  assume h,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume ptoq,
  apply or.elim (em P),
  assume p,
  have q : Q := ptoq p,
  apply or.intro_right,
  exact q,
  assume np,
  apply or.intro_left,
  exact np,
  assume npq,
  assume p,
  have porq : P ∨ Q,
  apply or.intro_left,
  exact p,
  cases npq,
  cases porq,
  contradiction,
  exact porq,
  exact npq,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume ptoq,
  assume nq,
  assume p,
  have q : Q := ptoq p,
  have f := nq q,
  exact f,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npnq,
  assume q,
  apply or.elim (em P),
  assume p,
  exact p,
  assume np,
  have nq : ¬Q := npnq np,
  contradiction,
end

