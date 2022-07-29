import algebra.category.Mon

noncomputable theory

universes u v

variables (M : Type u)

lemma M_is_monoid : monoid M
:= {
  mul := sorry,
  one := sorry,
  one_mul :=
  begin
    intro a,
    have my_goal : (1 * a = a),
      by sorry,
    exact my_goal,
  end,
  mul_one := sorry,
  mul_assoc := sorry,
}