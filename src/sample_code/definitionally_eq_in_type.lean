import category_theory.closed.cartesian
import category_theory.limits.types
import category_theory.limits.shapes.types
import category_theory.types

noncomputable theory

universes u v

open category_theory
open category_theory.limits
open category_theory.limits.types
open category_theory.concrete_category

instance : monoidal_category (Type u) :=
  monoidal_of_has_finite_products (Type u)


-- the following doesn't compile
-- def as_from_prod (A B N : Type u) (f : A ⊗ B ⟶ N) : (A × B ⟶ N) := f,