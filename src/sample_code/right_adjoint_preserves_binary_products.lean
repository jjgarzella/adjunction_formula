import category_theory.limits.preserves.basic
import category_theory.limits.has_limits
import category_theory.adjunction.basic
import category_theory.closed.cartesian

import category_theory.limits.preserves.shapes.binary_products


set_option pp.universes true

noncomputable theory



universes u v

open category_theory
open category_theory.limits
open category_theory.adjunction

variables {C : Type u} [category.{v} C] [has_limits C]
variables {D : Type u} [category.{v} D] [has_limits D]
variables (F : C ⥤ D) (G : D ⥤ C) [adj : F ⊣ G]
include adj

variables (x y : D)

lemma RAPL_binary_products (a b : D) : G.obj (a ⨯ b) ≅ (G.obj a) ⨯ (G.obj b)
:=
begin
  haveI pres_all : preserves_limits_of_size.{0 0} G,
    by exact right_adjoint_preserves_limits adj,
  apply preserves_limit_pair.iso
  -- exact preserves_limit_pair.iso G a b
end

