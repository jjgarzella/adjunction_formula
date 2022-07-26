import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types
import algebra.category.Mon
set_option pp.universes true

noncomputable theory

universes u v


open category_theory
open category_theory.limits
open category_theory.limits.types

--#check types.has_limits_of_size (Type u)

-- variables (N : Mon)

-- #check (monoid.one)

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)


lemma Mon__of_monoid {M : Mon.{u}} : Mon_ (Type u) :=
{
  X := M,
  one := (λ _, (monoid.one)),
  mul :=
  begin
    have h1 : (↥M ⊗ ↥M) = (↥M ⨯ ↥M),
      by refl,
    have h2 : (↥M ⨯ ↥M) ≅ (↥M × ↥M),
      by apply types.binary_product_iso,
    --have h3 : ((↥M × ↥M) ⟶ ↥M) = ((↥M × ↥M) → ↥M),
    --  by refl,
    rw [h1],
    equiv_rw [iso.to_equiv h2],
  let curried : M × M → M := (λ x, x.1 * x.2),
  exact curried
  --exact (λ ((a,b) : (M × M)), (a*b))
  end,
  one_mul' := sorry,
  mul_one' := sorry,
  mul_assoc' := sorry,
}