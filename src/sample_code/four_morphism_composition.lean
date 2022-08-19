
import category_theory.category.basic

universes u v

open category_theory

variables (C : Type u) [category C]


lemma rearrange_comp (a b c d e : C) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (j : d ⟶ e) :
(f ≫ g) ≫ h ≫ j = (f ≫ (g ≫ h)) ≫ j :=
begin
  simp,
end

--theorem rearrage_composition :
--      (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--      as_hom (prod.map M.one (𝟙 M.X))) ≫
--      (binary_product_iso M.X M.X).symm.hom ≫
--      M.mul =
--      (as_hom (prod.map terminal_iso.inv (𝟙 M.X)) ≫
--      (as_hom (prod.map M.one (𝟙 M.X)) ≫
--      (binary_product_iso M.X M.X).symm.hom)) ≫
--      M.mul,
--      begin
--        -- simp,
--        -- simp,
--        sorry,
--      end,
--