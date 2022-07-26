import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types
set_option pp.universes true

noncomputable theory

universes u v


open category_theory
open category_theory.limits
open category_theory.limits.types

--#check types.has_limits_of_size (Type u)

#check monoidal_of_has_finite_products (Type u)

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)

#check Mon_ (Type u)

variables (N : Mon_ (Type u))
#check N.one_mul

lemma monoid_of_Mon__Types (M : Mon_ (Type u)) : monoid M.X :=
{
  one :=
  begin
    have h1 : 𝟙_ (Type u) = terminal (Type u),
      by refl,
    have h2 : terminal (Type u) ≅ punit := terminal_iso,
    have st : 𝟙_ (Type u),
      rw [h1],
      equiv_rw [iso.to_equiv h2],
      exact punit.star,
    exact (M.one st)
  end ,
  mul :=
  begin
    have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
    have h1 : (M.X ⊗ M.X) = (M.X ⨯ M.X),
      by refl,
    have h2 : (M.X ⨯ M.X) ≅ (M.X × M.X),
      by apply types.binary_product_iso,
    have h3 : ((M.X × M.X) ⟶ M.X) = ((M.X × M.X) → M.X),
      by refl,
    rw [h1] at hmul,
    equiv_rw [iso.to_equiv h2] at hmul,
    --rw [h3] at hmul,
    exact (λ a b, hmul (a,b)),
  end,
  mul_assoc := sorry,
  one_mul :=
  begin
    let om := M.one_mul,
    sorry
  end,
  mul_one := sorry,
}