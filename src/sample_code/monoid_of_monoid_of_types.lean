import category_theory.closed.cartesian
import category_theory.limits.has_limits
import category_theory.monoidal.Mon_
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types

-- set_option pp.universes true
-- set_option pp.implicit true
-- set_option trace.simplify.rewrite true


noncomputable theory

universes u v


open category_theory
-- open category_theory.limits
open category_theory.limits.types
open category_theory.concrete_category

--#check types.has_limits_of_size (Type u)

-- #check monoidal_of_has_finite_products (Type u)

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)



-- #check Mon_ (Type u)

-- #check hom_ext

-- #check binary_product_iso


-- variables (N : Mon_ (Type u))
-- #check (⇑ N.mul)

-- variables (Nmul' : (N.X ⨯ N.X) ⟶ N.X)
-- #check (⇑ Nmul')
-- #check has_one ↑(

-- #check has_one ↑(

-- lemma type_prod_iso_monoidal_prod (A B : (Type u)) :
-- (A ⊗ B) ≅ (A × B)
-- := by apply binary_product_iso

-- lemma terminal_iso_punit : 𝟙_ (Type u) ≅ punit
-- := by apply terminal_iso

instance has_one_of_Mon__Type (M : Mon_ (Type u)) : has_one M.X :=
{ one := ((terminal_iso.symm.hom ≫ M.one) punit.star) }
  -- begin
  --   -- have h1 : 𝟙_ (Type u) = terminal (Type u),
  --   --   by refl,
  --   -- have h2 : 𝟙_ (Type u) ≅ punit := terminal_iso,
  --   have hterm : punit ⟶ M.X
  --     := terminal_iso.symm.hom ≫ M.one,
  --   -- have st : 𝟙_ (Type u),
  --     -- rw [h1],
  --     -- equiv_rw [iso.to_equiv terminal_iso_punit],
  --     -- exact punit.star,
  --   exact (hterm punit.star)
  -- end

-- (A ⨯ B) = (A × B)
-- #check binary_product_iso


-- def as_from_prod (A B N : Type u) (f : A ⊗ B ⟶ N) : (A × B ⟶ N) :=
-- begin
--   have definitionally_equal : A ⊗ B = (A × B),
--     by simp,
--   rw [definitionally_equal] at f,
--   exact f,
--     -- begin
--       -- unfold category_theroy.monoidal_of_has_finite_product.tensor_obj,
--       -- unfold limits.prod,
-- --
--     -- end
-- end

-- #check limits.prod.map

instance has_mul_of_Mon__Type (M : Mon_ (Type u)) : has_mul M.X :=
{ mul := (λ a b, ((binary_product_iso _ _).symm.hom ≫ M.mul) (a,b)) }
-- { mul :=  ((binary_product_iso _ _).symm.hom ≫ M.mul) }
  -- begin
    -- have hmul : (M.X × M.X) ⟶ M.X
      -- := ((binary_product_iso _ _).symm.hom ≫ M.mul),
    -- have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
    -- equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod M.X M.X)] at hmul,
    -- rw [h3] at hmul,
    -- exact (λ a b, hmul (a,b)),
  -- end

-- why does it see the instance in tactic mode but not in term mode?
-- def has_mul_morphism (M : Mon_ (Type u)) : M.X × M.X ⟶ M.X :=
-- begin
--   exact (λ a, has_mul.mul a.fst a.snd)
-- end

-- why does it see binary_prod_iso in tactic/term mode but not in the type?
-- lemma mul_factors (M : Mon_ (Type u)) :
--       (binary_prod_iso _ _).symm.hom >> M.mul = has_mul_morphism :=

-- lemma prod_equiv_curry (M : Mon_(Type u)) :
-- M.X × M.X → M.X ≃ M.X → M.X → M.X :=
-- by sorry,

@[simp, reassoc]
lemma binary_product_iso_limits_fst_eq_fst (A B : Type u) :
  (binary_product_iso A B).inv ≫ limits.prod.fst = prod.fst :=
limits.prod.lift_fst _ _

@[simp, reassoc]
lemma binary_product_iso_limits_snd_eq_snd (A B : Type u) :
  (binary_product_iso A B).inv ≫ limits.prod.snd = prod.snd :=
limits.prod.lift_snd _ _

def punit_prod_iso (A : Type u) : (punit : (Type u)) × A ≅ A :=
  (binary_product_iso _ _).symm ≪≫
  tensor_iso terminal_iso.symm (iso.refl _) ≪≫
  (λ_ A)

def punit_morph_prod (M : Mon_ (Type u)) : (punit : Type u) × M.X ⟶ M.X × M.X :=
  (binary_product_iso _ _).symm.hom ≫
  (tensor_iso terminal_iso.symm (iso.refl _)).hom ≫
  (M.one ⊗ (𝟙 M.X)) ≫
  (binary_product_iso _ _).hom

lemma prod_map_bpo_commutes (A B C D : Type u) (f : A ⟶ C) (g : B ⟶ D) :
as_hom (prod.map f g) ≫
(binary_product_iso C D).inv =
(binary_product_iso A B).inv ≫
limits.prod.map f g :=
by { ext1; simpa }
--begin
--  apply category_theory.limits.prod.hom_ext,
--  -- prod.fst, goal 1
--  apply funext, intros x,
--  conv_lhs {
--    simp only [category_theory.types_comp_apply,
--               category_theory.limits.types.binary_product_iso_inv_comp_fst_apply],
--  },
--  conv_rhs {
--    simp only [category_theory.limits.prod.map_fst,
--                         category_theory.iso.cancel_iso_inv_left,
--                         eq_self_iff_true,
--                         category_theory.category.assoc],
--    simp only [category_theory.types_comp_apply,
--                 eq_self_iff_true,
--                 category_theory.limits.types.binary_product_iso_inv_comp_fst_apply]
--  },
--  refl,
--  -- prod.snd, goal 2
--  apply funext, intros x,
--  conv_lhs {
--    simp only [category_theory.types_comp_apply,
--               category_theory.limits.types.binary_product_iso_inv_comp_snd_apply],
--  },
--  conv_rhs {
--    simp only [category_theory.limits.prod.map_snd,
--                         category_theory.iso.cancel_iso_inv_left,
--                         eq_self_iff_true,
--                         category_theory.category.assoc],
--    simp only [category_theory.types_comp_apply,
--                 eq_self_iff_true,
--                 category_theory.limits.types.binary_product_iso_inv_comp_snd_apply]
--  },
--  refl,
--end



lemma monoid_of_Mon__Type (M : Mon_ (Type u)) : monoid M.X :=
{
  one := has_one.one,
  mul := has_mul.mul,
  mul_assoc := sorry,
  one_mul :=
  begin
  --  have punit_prod_iso : (punit : Type u) × M.X ≅ M.X :=
  --    (binary_product_iso _ _).symm ≪≫
  --    tensor_iso terminal_iso.symm (iso.refl _) ≪≫
  --    (λ_ M.X),

    -- have terminal_prod_iso : (𝟙_ (Type u)) × M.X ≅ M.X :=
    --   (binary_product_iso _ _).symm ≪≫
    --   (λ_ M.X),
    -- have punit_morph_prod : (punit : Type u) × M.X ⟶ M.X × M.X :=
      -- (binary_product_iso _ _).symm.hom ≫
      -- (tensor_iso terminal_iso.symm (iso.refl _)).hom ≫
      -- (M.one ⊗ (𝟙 M.X)) ≫
      -- (binary_product_iso _ _).hom,
    have mul := M.mul,
    let om := M.one_mul,

    intro a,
    have morph_one_a : (prod.map (terminal_iso.symm.hom ≫ M.one) (𝟙 M.X)) (punit.star,a) =
      ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
      by simp,
    have morph_one_comp_a :
      (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
      as_hom (prod.map M.one (𝟙 M.X))) (punit.star, a) =
      ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
      begin
        simp,
        refl,
      end,

    unfold has_mul.mul,
    unfold has_one.one,
    -- type_check types_comp_apply,
    -- type_check prod.lift,
    -- type_check prod.map,
    rw [←morph_one_comp_a],
    -- rw [←(types_comp_apply (prod.map (terminal_iso.symm.hom ≫ M.one) (𝟙 M.X))
      -- ((binary_product_iso M.X M.X).symm.hom ≫ M.mul))],
    rw [←(types_comp_apply (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
                           as_hom (prod.map M.one (𝟙 M.X)))
                           ((binary_product_iso M.X M.X).symm.hom ≫
                           M.mul))],


    have comm_rectangle_terminal_iso:
      as_hom (prod.map (terminal_iso.symm.hom) (𝟙 M.X)) ≫
      (binary_product_iso _ _).symm.hom =
      (binary_product_iso _ _).symm.hom ≫
      ((terminal_iso.symm.hom) ⊗ (𝟙 M.X)), -- you have to have the outer parens
      by { simp, apply prod_map_bpo_commutes },

    have comm_rectangle_prod_map :
      as_hom (prod.map M.one (𝟙 M.X)) ≫
      (binary_product_iso _ _).symm.hom =
      (binary_product_iso _ _).symm.hom ≫
      (M.one ⊗ (𝟙 M.X)), -- you have to have the outer parens
      by { simp, apply prod_map_bpo_commutes },

    have rearrage_composition :
      (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
      as_hom (prod.map M.one (𝟙 M.X))) ≫
      (binary_product_iso M.X M.X).symm.hom ≫
      M.mul =
      (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
      (as_hom (prod.map M.one (𝟙 M.X)) ≫
      (binary_product_iso M.X M.X).symm.hom)) ≫
      M.mul,
      begin
        -- simp,
        -- simp,
        sorry,
      end,



    -- rw [comm_rectangle_prod_map],
    -- have morph_version :
    --   ((punit_prod_iso M.X).symm.hom ≫ (punit_morph_prod M)) a =
    --   ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
    --   begin
    --     -- simp,
    --     unfold punit_morph_prod,
    --     unfold punit_prod_iso,
    --     -- slice_lhs 1 2 { },
    --     simp [punit_prod_iso],
    --   end,

    -- have punit_prod_iso : ((punit : Type u) × M.X) ≅ ((𝟙_ (Type u)) ⨯ M.X)
    --   := (binary_product_iso _ _).symm ≪≫ tensor_iso terminal_iso.symm (iso.refl _),

    sorry,

    -- simp [punit_prod_iso, binary_coproduct_iso, M.one_mul],


    -- let comp_left_one_mul := (M.one ⊗ 𝟙 M.X) ≫ M.mul,
    -- let lcomb := (λ_ M.X).hom,
    -- have blah_isom : (𝟙_ (Type u) ⊗ M.X) ≅ ((𝟙_ (Type u)) × M.X),
      -- by apply binary_product_iso,

    -- have lcomb_correct_type : (punit × M.X) → M.X,
    --   begin
    --     equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
    --       at lcomb,
    --     equiv_rw [iso.to_equiv terminal_iso_punit] at lcomb,
    --     exact lcomb
    --   end,
    -- have comp_left_one_mul_correct_type : (punit × M.X) → M.X,
    --   begin
    --     equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
    --       at comp_left_one_mul,
    --     equiv_rw [iso.to_equiv terminal_iso_punit] at comp_left_one_mul,
    --     exact comp_left_one_mul
    --   end,
    -- intro a,
    -- have left : (comp_left_one_mul_correct_type (punit.star,a)) = 1 * a,
    --   by sorry,
    --   have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
    --   equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod M.X M.X)] at hmul,
    --   have step_one : hmul (1,a) = 1 * a,
    --     unfold has_mul.mul,
    --     simp,
    --   sorry,
    -- have right : (lcomb_correct_type (punit.star,a) = a),
    --   begin
    --     have step : lcomb_correct_type = prod.snd,
    --       begin
    --         sorry,
    --       end,
    --     rw [step],
    --   end,
    -- have left_eq_right : lcomb_correct_type = comp_left_one_mul_correct_type,
    --   by sorry,
    -- rw [←left],
    -- conv_rhs { rw [←right] },
    -- rw [left_eq_right],
    -- --simp [left_eq_right],
    -- -- congr_fun left_eq_right (punit.star,a)



    -- suffices h : (M.one ⊗ 𝟙 M.X) ≫ M.mul = (λ_ M.X).hom,
    -- have left : (((M.one ⊗ 𝟙 M.X) ≫ M.mul) (punit.star,a) = 1 * a,
      -- by sorry,
    -- have right : (λ_ M.X).hom a = a,
      -- by sorry,
    -- sorry
  end,
  mul_one := sorry,
}