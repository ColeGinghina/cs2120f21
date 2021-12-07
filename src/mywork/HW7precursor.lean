def cong_mod (n a b : ℤ) : Prop :=
  ∃ k, a - b = k * n

def cong_mod_n_is_equiv_relation (n : ℤ) : Prop :=
  equivalence (cong_mod n)

example : cong_mod (4:ℤ) (6:ℤ) (14:ℤ) :=
begin
  unfold cong_mod,
  apply exists.intro (-2:ℤ),
  refl,
end