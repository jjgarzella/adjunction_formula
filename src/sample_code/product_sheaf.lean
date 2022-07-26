import category_theory.limits.preserves.basic
import category_theory.limits.has_limits
--import category_theory.closed.cartesian
import category_theory.sites.sheaf
import category_theory.sites.limits
import category_theory.opposites

import category_theory.limits.preserves.shapes.binary_products

--set_option pp.universes true

noncomputable theory



universes v u

open category_theory
open category_theory.limits
open category_theory.Sheaf.category_theory.limits
open opposite


variables {C : Type u} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type u} [category.{v} D] [has_limits D]
variables (F : (Sheaf J D))

--#check limits.evaluation_preserves_limits

variables (V : C)

--#check (evaluation C D).obj V



--lemma forgetful_functor_preserves_products : (F ⨯ F).val ≅ (F.val ⨯ F.val) := sorry

lemma eval_defn (U : C) (G : Cᵒᵖ ⥤ D) :
(G.obj (op U)) = (((evaluation Cᵒᵖ D).obj (op U)).obj G)
:= by refl

lemma explicit_sheaf_prod (U : C) :
(F.val ⨯ F.val).obj (op U) ≅ ((F.val.obj (op U)) ⨯ (F.val.obj (op U))) :=
begin
  -- have h_indvl : (F.val.obj (op U)) = (((evaluation Cᵒᵖ D).obj (op U)).obj F.val),
  --   by refl,
  -- have h_prod :
  rw [eval_defn U F.val],
  rw [eval_defn U (F.val ⨯ F.val)],
  haveI : preserves_limits_of_size ((evaluation Cᵒᵖ D).obj (op U)),
    by apply limits.evaluation_preserves_limits,
  apply preserves_limit_pair.iso
end
