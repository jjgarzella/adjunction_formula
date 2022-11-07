import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types
import category_theory.monoidal.types

-- set_option pp.universes true
-- set_option pp.implicit true
-- set_option trace.simplify.rewrite true


noncomputable theory

universes u v


open category_theory
open category_theory.limits.types
open category_theory.concrete_category

variables (N : Mon_ (Type u))
-- instance : monoidal_category (Type u) :=
--   by apply_instance
  -- monoidal_of_has_finite_products (Type u)

instance has_one_of_Mon__Type (M : Mon_ (Type u)) : has_one M.X :=
{ one := (( M.one) punit.star) }

instance has_mul_of_Mon__Type (M : Mon_ (Type u)) : has_mul M.X :=
{ mul := (λ a b, M.mul (a,b)) }

@[simp, reassoc]
lemma binary_product_iso_limits_fst_eq_fst (A B : Type u) :
  (binary_product_iso A B).inv ≫ limits.prod.fst = prod.fst :=
limits.prod.lift_fst _ _

@[simp, reassoc]
lemma binary_product_iso_limits_snd_eq_snd (A B : Type u) :
  (binary_product_iso A B).inv ≫ limits.prod.snd = prod.snd :=
limits.prod.lift_snd _ _

-- def punit_prod_iso (A : Type u) : (punit : (Type u)) × A ≅ A :=
--   (binary_product_iso _ _).symm ≪≫
--   tensor_iso terminal_iso.symm (iso.refl _) ≪≫
--   (λ_ A)

-- def punit_morph_prod (M : Mon_ (Type u)) : (punit : Type u) × M.X ⟶ M.X × M.X :=
--   (binary_product_iso _ _).symm.hom ≫
--   (tensor_iso terminal_iso.symm (iso.refl _)).hom ≫
--   (M.one ⊗ (𝟙 M.X)) ≫
--   (binary_product_iso _ _).hom

-- lemma prod_map_bpo_commutes (A B C D : Type u) (f : A ⟶ C) (g : B ⟶ D) :
-- as_hom (prod.map f g) ≫
-- (binary_product_iso C D).inv =
-- (binary_product_iso A B).inv ≫
-- limits.prod.map f g :=
-- by { ext1; simpa }

-- lemma rearrange_comp (a b c d e : Type u) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (j : d ⟶ e) :
-- (f ≫ g) ≫ h ≫ j = (f ≫ (g ≫ h)) ≫ j :=
-- by simp

-- lemma rearrange_comp_2  (a b c d e : Type u) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (j : d ⟶ e) :
-- (f ≫ g ≫ h) ≫ j = (f ≫ g) ≫ h ≫ j :=
-- by simp?m_1 ⨯ ?m_2 ≅ ?m_1 × ?m_2

--?m_1 ⨯ ?m_2 ⟶ ?m_1 × ?m_2

lemma assoc_product (A : Type u) : (A × (A × A)) ≅ ((A × A) × A) :=
begin
  obviously,
  ext; simp,
  -- by library_search,
 --refine {hom := _ A, inv := _ A, hom_inv_id' := _, inv_hom_id' := _}
end

-- lemma assoc_product_2 (A : Type u) : A × (A × A) ⟶ (A × A) × A :=
-- begin
-- end

lemma monoid_of_Mon__Type (M : Mon_ (Type u)) : monoid M.X :=
{
  one := has_one.one,
  mul := has_mul.mul,
  mul_assoc := by λ x y z, convert congr_fun M.mul_assoc ((x y), z),
  -- begin
  --   intros a b c,
  --   dsimp [has_mul.mul],
  --   let bpo := (binary_product_iso _ _).hom,
  --   -- have : (bpo ⊗ 𝟙 M.X) ≫ (has_mul.mul ⊗ 𝟙 M.X) ≫ bpo ≫ has_mul.mul =
  --   --   (α_ M.X M.X M.X).hom ≫ 𝟙 M.X ⊗ bpo ≫ 𝟙 M.X ⊗ has_mul.mul ≫ bpo ≫ has_mul.mul,
  --   --   { sorry },

  --   type_check M.mul_assoc,
  --   type_check (binary_product_iso _ _)
  -- end,
  one_mul :=
  begin
    intro a,
    dsimp [has_mul.mul, has_one.one],
    have : (binary_product_iso _ _).inv ≫ (M.one ⊗ 𝟙 M.X) ≫ M.mul =
      (binary_product_iso _ _).inv ≫ (λ_ M.X).hom,
      { rw M.one_mul },
    convert _root_.congr_fun this (terminal_iso.inv punit.star, a),
    { have : function.injective (binary_product_iso M.X M.X).hom,
      { rw ← mono_iff_injective, apply_instance },
      apply this,
      ext; simp [elementwise_of (limits.prod.map_fst M.one (𝟙 M.X)),
        elementwise_of (limits.prod.map_snd M.one (𝟙 M.X))] },
    { simp },
  end,
  mul_one :=
  begin
    intro a,
    dsimp [has_mul.mul, has_one.one],
    have : (binary_product_iso _ _).inv ≫ (𝟙 M.X ⊗ M.one) ≫ M.mul =
      (binary_product_iso _ _).inv ≫ (ρ_ M.X).hom,
      by rw M.mul_one,
    convert _root_.congr_fun this (a, terminal_iso.inv punit.star),
    { have : function.injective (binary_product_iso M.X M.X).hom,
      { rw ← mono_iff_injective, apply_instance },
      apply this,
      ext; simp [elementwise_of (limits.prod.map_fst (𝟙 M.X) M.one),
        elementwise_of (limits.prod.map_snd (𝟙 M.X) M.one)], },
    { simp },
  end,
}