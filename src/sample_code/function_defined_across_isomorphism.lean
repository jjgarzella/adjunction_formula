import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types

noncomputable theory

universes u v

open category_theory
open category_theory.limits
open category_theory.limits.types
open category_theory.concrete_category

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)

variables {A : (Type u)}

lemma type_prod_iso_monoidal_prod (A B : (Type u)) :
(A ⊗ B) ≅ (A × B)
:= by apply types.binary_product_iso

lemma terminal_iso_punit : 𝟙_ (Type u) ≅ punit
:= by apply terminal_iso

def lcomb_correct_type
: (punit × A) → A :=
begin
  let lcomb := (λ_ A).hom,
  equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) A)]
    at lcomb,
  equiv_rw [iso.to_equiv terminal_iso_punit] at lcomb,
  exact lcomb
end

theorem elementwise_lcomb (a : A) : lcomb_correct_type (punit.star,a) = a :=
begin
  have step : lcomb_correct_type = prod.snd,
    begin
      sorry,
    end,
  rw [step],
end

