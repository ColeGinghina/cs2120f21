example : 0 ≠ 1 :=
begin
  assume h,
  cases h,
end 

example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  apply false.elim,
  contradiction,
end

-- or

example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f), -- use false.elim because proving a false statement
end

example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  -- ¬¬P
  -- ¬ P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f, -- or ignore the last two lines and write contradiction
  -- can also do case analysis
end 

axiom em : ∀ (P : Prop), P ∨ ¬P

theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume p,
  have pornp := classical.em P,
  cases pornp with p np,
  assumption, -- or exact p
  contradiction,
end

def pythagorean_triple (a b c : ℕ) : Prop :=
  a * a + b * b = c * c

example : ∃ (a b c : ℕ), pythagorean_triple 3 4 5 :=
begin
  
end

example : pythagorean_triple 3 4 5 :=
begin
  unfold pythagorean_triple,
  apply eq.refl,
end

example : pythagorean_triple 3 4 6 :=
begin
  unfold pythagorean_triple,
  apply eq.refl,
end