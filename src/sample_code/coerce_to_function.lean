import category_theory.types
import category_theory.limits.shapes.types
import category_theory.concrete_category.basic

noncomputable theory

universes u v

open category_theory
--open category_theory.concrete_category

variables (M : Type u)
variables (F : (M ⨯ M) ⟶ M)

--instance : has_coe_to_fun ((M ⨯ M) ⟶ M) (λ f, (M ⨯ M) → M)
--:= concrete_category.has_coe_to_fun

instance {A B : Type u} : has_coe_to_fun (A ⟶ B) (λ f, A → B)
:= concrete_category.has_coe_to_fun

#check (⇑ F)