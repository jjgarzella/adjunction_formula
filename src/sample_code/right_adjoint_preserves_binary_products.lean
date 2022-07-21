import category_theory.limits.preserves.basic
import category_theory.limits.has_limits
import category_theory.adjunction.basic
import category_theory.closed.cartesian

noncomputable theory

universes u v

open category_theory
open category_theory.limits
open category_theory.adjunction

variables {C : Type u} [category.{v} C] [has_limits C]
variables {D : Type u} [category.{v} D] [has_limits D]
variables (F : C ⥤ D) (G : D ⥤ C) [adj : F ⊣ G]
include adj

lemma RAPL_binary_products (a b : D) : G.obj (a ⨯ b) ≅ (G.obj a) ⨯ (G.obj b) 
:= 
begin
  have pres : preserves_limits_of_size G,
    by exact right_adjoint_preserves_limits adj,
  apply_instance,
  -- What goes here? 
  -- Pretty sure I should not be unfolding the definition into limit cones
end

