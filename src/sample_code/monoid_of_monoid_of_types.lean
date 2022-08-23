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
open category_theory.limits.types
open category_theory.concrete_category

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)

instance has_one_of_Mon__Type (M : Mon_ (Type u)) : has_one M.X :=
{ one := ((terminal_iso.symm.hom ≫ M.one) punit.star) }

instance has_mul_of_Mon__Type (M : Mon_ (Type u)) : has_mul M.X :=
{ mul := (λ a b, ((binary_product_iso _ _).symm.hom ≫ M.mul) (a,b)) }

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

lemma rearrange_comp (a b c d e : Type u) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (j : d ⟶ e) :
(f ≫ g) ≫ h ≫ j = (f ≫ (g ≫ h)) ≫ j :=
by simp

lemma rearrange_comp_2  (a b c d e : Type u) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (j : d ⟶ e) :
(f ≫ g ≫ h) ≫ j = (f ≫ g) ≫ h ≫ j :=
by simp

lemma one_mul_of_Mon__Type (M : Mon_ (Type u)) : ∀ (a : M.X), 1 * a = a :=
begin
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
      simp only [category_theory.types_comp_apply, category_theory.iso.symm_hom],
      refl,
    end,

  have comm_rectangle_terminal_iso:
    as_hom (prod.map (terminal_iso.inv) (𝟙 M.X)) ≫
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

  have rearrange_composition :
    (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
    as_hom (prod.map M.one (𝟙 M.X))) ≫
    (binary_product_iso M.X M.X).symm.hom ≫
    M.mul =
    (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
    (as_hom (prod.map M.one (𝟙 M.X)) ≫
    (binary_product_iso M.X M.X).symm.hom)) ≫
    M.mul,
    begin
      by apply rearrange_comp,
      -- simp,
      -- `simp` should work here, at the time of writing this comment it seems to time out
    end,

  have rearrange_composition_2 :
    ((as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
    (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom ≫
    (M.one ⊗ 𝟙 M.X)) ≫
    M.mul) =
    (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
    (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom) ≫
    (M.one ⊗ 𝟙 M.X) ≫
    M.mul,
    by apply rearrange_comp_2,

  have same_morphism :
    (binary_product_iso (⊤_ Type u) M.X).symm.hom = (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom,
    by refl,

  have ppo_equality :
    (((binary_product_iso punit M.X).symm.hom ≫ (terminal_iso.symm.hom ⊗ 𝟙 M.X)) ≫ (λ_ M.X).hom)
    = prod.snd,
    by simp,

  unfold has_mul.mul,
  unfold has_one.one,
  rw [←morph_one_comp_a],
  rw [←(types_comp_apply (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
                         as_hom (prod.map M.one (𝟙 M.X)))
                         ((binary_product_iso M.X M.X).symm.hom ≫
                         M.mul))],

  rw [rearrange_composition],
  rw [comm_rectangle_prod_map],
  rw [rearrange_composition_2],
  rw [←same_morphism],
  rw [comm_rectangle_terminal_iso],
  rw [om],
  rw [ppo_equality],
end

-- lemma monoid_of_Mon__Type (M : Mon_ (Type u)) : monoid M.X :=
-- {
--   one := has_one.one,
--   mul := has_mul.mul,
--   mul_assoc := sorry,
--   one_mul :=
--   begin
--   --  have punit_prod_iso : (punit : Type u) × M.X ≅ M.X :=
--   --    (binary_product_iso _ _).symm ≪≫
--   --    tensor_iso terminal_iso.symm (iso.refl _) ≪≫
--   --    (λ_ M.X),

--     -- have terminal_prod_iso : (𝟙_ (Type u)) × M.X ≅ M.X :=
--     --   (binary_product_iso _ _).symm ≪≫
--     --   (λ_ M.X),
--     -- have punit_morph_prod : (punit : Type u) × M.X ⟶ M.X × M.X :=
--       -- (binary_product_iso _ _).symm.hom ≫
--       -- (tensor_iso terminal_iso.symm (iso.refl _)).hom ≫
--       -- (M.one ⊗ (𝟙 M.X)) ≫
--       -- (binary_product_iso _ _).hom,
--     have mul := M.mul,
--     let om := M.one_mul,

--     intro a,
--     have morph_one_a : (prod.map (terminal_iso.symm.hom ≫ M.one) (𝟙 M.X)) (punit.star,a) =
--       ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
--       by simp,
--     have morph_one_comp_a :
--       (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--       as_hom (prod.map M.one (𝟙 M.X))) (punit.star, a) =
--       ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
--       begin
--         simp,
--         refl,
--       end,

--     unfold has_mul.mul,
--     unfold has_one.one,
--     -- type_check types_comp_apply,
--     -- type_check prod.lift,
--     -- type_check prod.map,
--     rw [←morph_one_comp_a],
--     -- rw [←(types_comp_apply (prod.map (terminal_iso.symm.hom ≫ M.one) (𝟙 M.X))
--       -- ((binary_product_iso M.X M.X).symm.hom ≫ M.mul))],
--     rw [←(types_comp_apply (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--                            as_hom (prod.map M.one (𝟙 M.X)))
--                            ((binary_product_iso M.X M.X).symm.hom ≫
--                            M.mul))],


--     have comm_rectangle_terminal_iso:
--       as_hom (prod.map (terminal_iso.inv) (𝟙 M.X)) ≫
--       (binary_product_iso _ _).symm.hom =
--       (binary_product_iso _ _).symm.hom ≫
--       ((terminal_iso.symm.hom) ⊗ (𝟙 M.X)), -- you have to have the outer parens
--       by { simp, apply prod_map_bpo_commutes },

--     have comm_rectangle_prod_map :
--       as_hom (prod.map M.one (𝟙 M.X)) ≫
--       (binary_product_iso _ _).symm.hom =
--       (binary_product_iso _ _).symm.hom ≫
--       (M.one ⊗ (𝟙 M.X)), -- you have to have the outer parens
--       by { simp, apply prod_map_bpo_commutes },

--     have rearrange_composition :
--       (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--       as_hom (prod.map M.one (𝟙 M.X))) ≫
--       (binary_product_iso M.X M.X).symm.hom ≫
--       M.mul =
--       (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--       (as_hom (prod.map M.one (𝟙 M.X)) ≫
--       (binary_product_iso M.X M.X).symm.hom)) ≫
--       M.mul,
--       begin
--         by apply rearrange_comp,
--         -- simp,
--         -- `simp` should work here, at the time of writing this comment it seems to time out
--       end,

--     have rearrange_composition_2 :
--       ((as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--       (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom ≫
--       (M.one ⊗ 𝟙 M.X)) ≫
--       M.mul) =
--       (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--       (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom) ≫
--       (M.one ⊗ 𝟙 M.X) ≫
--       M.mul,
--       by apply rearrange_comp_2,

--     have same_morphism :
--       (binary_product_iso (⊤_ Type u) M.X).symm.hom = (binary_product_iso (𝟙_ (Type u)) M.X).symm.hom,
--       by refl,

--     have ppo_equality :
--       (((binary_product_iso punit M.X).symm.hom ≫ (terminal_iso.symm.hom ⊗ 𝟙 M.X)) ≫ (λ_ M.X).hom)
--       = prod.snd,
--       by simp,




--     conv_lhs { rw [rearrange_composition] },
--     conv_lhs { rw [comm_rectangle_prod_map] },
--     conv_lhs { rw [rearrange_composition_2] },
--     rw [←same_morphism],
--     conv_lhs { rw [comm_rectangle_terminal_iso] },
--     conv_lhs { rw [om] },
--     conv_lhs { rw [ppo_equality] },

--     -- simp [punit_prod_iso],
--     -- exact (punit_prod_iso M.X).hom,


--     -- rw [←rearrange_comp],
--     -- conv_lhs { rw [comm_rectangle_terminal_iso] },

--     -- conv_lhs { rw [rearrange_composition] }

--     -- rw [comm_rectangle_prod_map],
--     -- have morph_version :
--     --   ((punit_prod_iso M.X).symm.hom ≫ (punit_morph_prod M)) a =
--     --   ((terminal_iso.symm.hom ≫ M.one) punit.star, a),
--     --   begin
--     --     -- simp,
--     --     unfold punit_morph_prod,
--     --     unfold punit_prod_iso,
--     --     -- slice_lhs 1 2 { },
--     --     simp [punit_prod_iso],
--     --   end,

--     -- have punit_prod_iso : ((punit : Type u) × M.X) ≅ ((𝟙_ (Type u)) ⨯ M.X)
--     --   := (binary_product_iso _ _).symm ≪≫ tensor_iso terminal_iso.symm (iso.refl _),

--     -- sorry,

--     -- simp [punit_prod_iso, binary_coproduct_iso, M.one_mul],


--     -- let comp_left_one_mul := (M.one ⊗ 𝟙 M.X) ≫ M.mul,
--     -- let lcomb := (λ_ M.X).hom,
--     -- have blah_isom : (𝟙_ (Type u) ⊗ M.X) ≅ ((𝟙_ (Type u)) × M.X),
--       -- by apply binary_product_iso,

--     -- have lcomb_correct_type : (punit × M.X) → M.X,
--     --   begin
--     --     equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
--     --       at lcomb,
--     --     equiv_rw [iso.to_equiv terminal_iso_punit] at lcomb,
--     --     exact lcomb
--     --   end,
--     -- have comp_left_one_mul_correct_type : (punit × M.X) → M.X,
--     --   begin
--     --     equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod (𝟙_ (Type u)) M.X)]
--     --       at comp_left_one_mul,
--     --     equiv_rw [iso.to_equiv terminal_iso_punit] at comp_left_one_mul,
--     --     exact comp_left_one_mul
--     --   end,
--     -- intro a,
--     -- have left : (comp_left_one_mul_correct_type (punit.star,a)) = 1 * a,
--     --   by sorry,
--     --   have hmul : M.X ⊗ M.X ⟶ M.X := M.mul,
--     --   equiv_rw [iso.to_equiv (type_prod_iso_monoidal_prod M.X M.X)] at hmul,
--     --   have step_one : hmul (1,a) = 1 * a,
--     --     unfold has_mul.mul,
--     --     simp,
--     --   sorry,
--     -- have right : (lcomb_correct_type (punit.star,a) = a),
--     --   begin
--     --     have step : lcomb_correct_type = prod.snd,
--     --       begin
--     --         sorry,
--     --       end,
--     --     rw [step],
--     --   end,
--     -- have left_eq_right : lcomb_correct_type = comp_left_one_mul_correct_type,
--     --   by sorry,
--     -- rw [←left],
--     -- conv_rhs { rw [←right] },
--     -- rw [left_eq_right],
--     -- --simp [left_eq_right],
--     -- -- congr_fun left_eq_right (punit.star,a)



--     -- suffices h : (M.one ⊗ 𝟙 M.X) ≫ M.mul = (λ_ M.X).hom,
--     -- have left : (((M.one ⊗ 𝟙 M.X) ≫ M.mul) (punit.star,a) = 1 * a,
--       -- by sorry,
--     -- have right : (λ_ M.X).hom a = a,
--       -- by sorry,
--     -- sorry
--   end,
--   mul_one := sorry,
-- }