import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types

-- set_option pp.universes true
set_option trace.simplify.rewrite true


noncomputable theory

universes u v


open category_theory
open category_theory.limits
open category_theory.limits.types
open category_theory.concrete_category

--#check types.has_limits_of_size (Type u)

-- #check monoidal_of_has_finite_products (Type u)

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)

-- #check Mon_ (Type u)

#check hom_ext



variables (N : Mon_ (Type u))
-- #check (⇑ N.mul)

-- variables (Nmul' : (N.X ⨯ N.X) ⟶ N.X)
-- #check (⇑ Nmul')
-- #check has_one ↑(

-- #check has_one ↑(

lemma type_prod_iso_monoidal_prod (A B : (Type u)) :
(A ⊗ B) ≅ (A × B)
:= by apply types.binary_product_iso

lemma terminal_iso_punit : 𝟙_ (Type u) ≅ punit
:= by apply terminal_iso

instance has_one_of_Mon__Type (M : Mon_ (Type u)) : has_one M.X :=
{ one :=
  begin
    -- have h1 : 𝟙_ (Type u) = terminal (Type u),
    --   by refl,
    -- have h2 : 𝟙_ (Type u) ≅ punit := terminal_iso,
    have hterm : punit ⟶ M.X
      := terminal_iso.symm.hom ≫ M.one,
    -- have st : 𝟙_ (Type u),
      -- rw [h1],
      -- equiv_rw [iso.to_equiv terminal_iso_punit],
      -- exact punit.star,
    exact (hterm punit.star)
  end
}

#check types.binary_product_iso

instance has_mul_of_Mon__Type (M : Mon_ (Type u)) : has_mul M.X :=
{ mul :=
  begin
    have hmul : (M.X × M.X) ⟶ M.X
      := ((types.binary_product_iso _ _).symm.hom ≫ M.mul),
    -- have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
    -- equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod M.X M.X)] at hmul,
    --rw [h3] at hmul,
    exact (λ a b, hmul (a,b)),
  end
}


-- lemma prod_equiv_curry (M : Mon_(Type u)) :
-- M.X × M.X → M.X ≃ M.X → M.X → M.X :=
-- by sorry,

lemma monoid_of_Mon__Type (M : Mon_ (Type u)) : monoid M.X :=
{
  one := has_one.one,
  mul := has_mul.mul,
  mul_assoc := sorry,
  one_mul :=
  begin
    let comp_left_one_mul := (M.one ⊗ 𝟙 M.X) ≫ M.mul,
    let lcomb := (λ_ M.X).hom,
    let om := M.one_mul,
    -- have blah_isom : (𝟙_ (Type u) ⊗ M.X) ≅ ((𝟙_ (Type u)) × M.X),
      -- by apply types.binary_product_iso,

    have lcomb_correct_type : (punit × M.X) → M.X,
      begin
        equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
          at lcomb,
        equiv_rw [iso.to_equiv terminal_iso_punit] at lcomb,
        exact lcomb
      end,
    have comp_left_one_mul_correct_type : (punit × M.X) → M.X,
      begin
        equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
          at comp_left_one_mul,
        equiv_rw [iso.to_equiv terminal_iso_punit] at comp_left_one_mul,
        exact comp_left_one_mul
      end,
    intro a,
    have left : (comp_left_one_mul_correct_type (punit.star,a)) = 1 * a,
      by sorry,
      have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
      equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod M.X M.X)] at hmul,
      have step_one : hmul (1,a) = 1 * a,
        unfold has_mul.mul,
        simp,
      sorry,
    have right : (lcomb_correct_type (punit.star,a) = a),
      begin
        have step : lcomb_correct_type = prod.snd,
          begin
            sorry,
          end,
        rw [step],
      end,
    have left_eq_right : lcomb_correct_type = comp_left_one_mul_correct_type,
      by sorry,
    rw [←left],
    conv_rhs { rw [←right] },
    rw [left_eq_right],
    --simp [left_eq_right],
    -- congr_fun left_eq_right (punit.star,a)



    -- suffices h : (M.one ⊗ 𝟙 M.X) ≫ M.mul = (λ_ M.X).hom,
    -- have left : (((M.one ⊗ 𝟙 M.X) ≫ M.mul) (punit.star,a) = 1 * a,
      -- by sorry,
    -- have right : (λ_ M.X).hom a = a,
      -- by sorry,
    -- sorry
  end,
  mul_one := sorry,
}