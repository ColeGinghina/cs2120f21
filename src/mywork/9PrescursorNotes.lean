/- 
Negation
-/

/-
What does it mean when we say "it is true that P is not true"?
-/

/-
If P were true then soemthing that is impossible would occur. Because
the impossible cannot happen, there must be no proof of P.
-/

example : false → false :=
begin
  assume f,
  exact f,
end

example : false → true :=
begin
  assume f,
  apply true.intro,
end

example : true → false :=
begin
  assume t,
  -- stuck
end

/-
It is this analysis that leads to the defintion of ¬ P. For
any proposition P, we define ¬ P to be the proposition, P → false.
What this means is that if there is a proof of P → false, then 
you can conclude ¬ P. This is the introduction rule for ¬.
-/

example : ¬ false :=
begin
  assume f,
  exact f,
end

example : ¬ (0 = 1) :=
begin
  assume h,
  cases h,
end

example : ∀ (P Q R : Prop), P ∨ Q → R :=
begin
  assume P Q R,
  assume pq,
  cases pq,
  -- stuck here
end 

example : false → false :=
begin
  assume f,
  exact false.elim f,
end

theorem false_elim (P : Prop) (f : false) : P :=
begin
  cases f,
end