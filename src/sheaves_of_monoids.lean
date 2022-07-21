import category_theory.sites.sheaf_of_types
import category_theory.sites.sheaf
import algebra.category.Mon.basic
import category_theory.monoidal.Mon_
import category_theory.closed.cartesian
import category_theory.sites.limits
import category_theory.limits.has_limits
import category_theory.opposites
--want to show:
--given a monoid object F in the category of sheaves of sets,
--  then F(U) has the structure of a monoid for any U in the source

-- set_option trace.class_instances true

open category_theory
open category_theory.limits
open category_theory.Sheaf.category_theory.limits
open category_theory.Sheaf
open opposite

noncomputable theory
-- universes u v

-- variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
-- #check monoidal_of_has_finite_products (Sheaf J (Type (max v u)))

universes u v w


variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
-- variables (F : Cᵒᵖ ⥤ Type (max v u)) [hf : presieve.is_sheaf J F]


variables (L : C) (F : Sheaf J (Type (max v u)))
#check (F.val).obj (op L)

-- #check @Mon_ (Sheaf J (Type (max v u))) _
-- -- (monoidal_of_has_finite_products (Sheaf J (Type (max v u))))

-- #check (monoidal_of_has_finite_products (Sheaf J (Type (max v u))))

instance : monoidal_category (Sheaf J (Type (max v u))) :=
(monoidal_of_has_finite_products (Sheaf J (Type (max v u))))

variables (N : Mon_ (Sheaf J (Type max v u)))

#check (N.X.val.obj (op L))
#check ((N.mul.val).app (op L))

#check ((Sheaf_to_presheaf J (Type (max v u))).obj N.X)
lemma blah1 : ((Sheaf_to_presheaf J (Type (max v u))).obj N.X) = N.X.val
:= by refl

lemma monoid_of_application_of_sheaf_of_monoids
(M : Mon_ (Sheaf J (Type (max v u)))
)
(U : C) : monoid ((M.X.val).obj (op U)) :=
{
  one := sorry,
  mul :=
    begin
      have M : Mon_ (Sheaf J (Type (max v u))),
        by assumption,
      -- step 1: this is actually a product
      have step1 : (M.X ⊗ M.X) = (M.X ⨯ M.X),
        by refl,
      -- step 2: we can pull the product through .val, i.e. the functor
      --         Sheaf_to_presheaf
      -- need to use that this (forgetful) functor preserves limits
      -- and thVis is because the forgetful functor is a right adjoint
      have step2 : (M.X ⨯ M.X).val = (M.X.val ⨯ M.X.val),
        have func_desc_single : ((Sheaf_to_presheaf J (Type (max v u))).obj M.X) = M.X.val,
          by refl,
        have func_desc_prod : ((Sheaf_to_presheaf J (Type (max v u))).obj (M.X ⨯ M.X)) =
                              (M.X ⨯ M.X).val,
          by refl,
        rw [←func_desc_prod],
        rw [←func_desc_single],
        sorry,
      -- step 3: something about natural transformations

      -- step 4: difference between category theory product and
      --         lean's curried/uncurried thing
      --exact (M.mul.val.app (op U))
      sorry
    end
  ,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
}

-- lemma monoid_of_application_of_sheaf_of_monoids(Sheaf J (Type (max v u)))
-- (M : @Mon_ (Sheaf J (Type (max v u))) _ (monoidal_of_has_finite_products (Sheaf J (Type (max v u))))
-- )
-- (U : C) : monoid ((M.X.val).obj (op U)) := sorry