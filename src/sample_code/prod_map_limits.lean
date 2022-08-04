import category_theory.closed.cartesian
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types

noncomputable theory

universes u v

open category_theory
-- open category_theory.limits
open category_theory.limits.types
open category_theory.concrete_category

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)


lemma prod_map_bpo_commutes (A B C D : Type u) (f : A ⟶ C) (g : B ⟶ D) :
as_hom (prod.map f g) ≫
(binary_product_iso C D).inv =
(binary_product_iso A B).inv ≫
limits.prod.map f g :=
begin
  apply category_theory.limits.prod.hom_ext,
  {
    apply funext, intros x,
    conv_lhs {
      simp only [category_theory.types_comp_apply,
                 category_theory.limits.types.binary_product_iso_inv_comp_fst_apply],
    },
    conv_rhs {
      simp only [category_theory.limits.prod.map_fst,
                           category_theory.iso.cancel_iso_inv_left,
                           eq_self_iff_true,
                           category_theory.category.assoc],
      simp only [category_theory.types_comp_apply,
                   eq_self_iff_true,
                   category_theory.limits.types.binary_product_iso_inv_comp_fst_apply]
    },
    refl,
  },
  {
    apply funext, intros x,
    conv_lhs {
      simp only [category_theory.types_comp_apply,
                 category_theory.limits.types.binary_product_iso_inv_comp_snd_apply],
    },
    conv_rhs {
      simp only [category_theory.limits.prod.map_snd,
                           category_theory.iso.cancel_iso_inv_left,
                           eq_self_iff_true,
                           category_theory.category.assoc],
      simp only [category_theory.types_comp_apply,
                   eq_self_iff_true,
                   category_theory.limits.types.binary_product_iso_inv_comp_snd_apply]
    },
    refl,
  }
end

  -- have prod_side :
    -- ((as_hom (prod.map f g) ≫
    -- (binary_product_iso C D).inv) ≫
    -- limits.prod.fst) x = f x.1,
    -- begin
      -- simp only [category_theory.types_comp_apply,
      --  category_theory.limits.types.binary_product_iso_inv_comp_fst_apply],
      -- refl,
    -- end,
  -- have limits_prod_side :
    -- (((binary_product_iso A B).inv ≫
    -- limits.prod.map f g) ≫
    -- limits.prod.fst) x = f x.1,
    -- begin
      -- have associate : (((binary_product_iso A B).inv ≫ limits.prod.map f g) ≫ limits.prod.fst) =
        -- (binary_product_iso A B).inv ≫ (limits.prod.map f g ≫ limits.prod.fst)
        -- := by simp only [category_theory.limits.prod.map_fst,
                        --  category_theory.iso.cancel_iso_inv_left,
                        --  eq_self_iff_true,
                        --  category_theory.category.assoc],
      -- rw [associate],
      -- rw [limits.prod.map_fst],
      -- simp only [category_theory.types_comp_apply,
                --  eq_self_iff_true,
                --  category_theory.limits.types.binary_product_iso_inv_comp_fst_apply],
    -- end,
  -- rw [prod_side, limits_prod_side],

  -- goal 2
  -- apply funext, intros x

  -- have ((as_hom (prod.map f g) ≫ (binary_product_iso C D).inv) ≫ limits.prod.fst) x = f x
