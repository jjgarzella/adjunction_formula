import ring_theory.derivation
import algebra.module.localized_module
import ring_theory.localization.basic
import algebra.algebra.basic

section localization
variables {R A SR : Type*} [comm_ring R] [comm_ring A]  [algebra R A]
variables  (S : submonoid R) 

instance : algebra.is_pushout R (localization S) A (localized_module S A) := sorry

end localization

section kaehler
noncomputable theory
variables {A B : Type*} [comm_ring A] [comm_ring B] [algebra B A] {S : submonoid B}

#check Ω[A⁄B]

--#check Ω[localizat⁄SB']


/-
 - Outline:
 - since localization is a tensor product:
 - (localized_module S Ω[A⁄B]) ≃ₗ[B] ((localization S) ⊗[B] Ω[A⁄B])
 -
 - kaehler_differential.derivation_tensor_product_equiv:
 - ((localization S) ⊗[B] Ω[A⁄B]) ≃ₗ[B] Ω[(localized_module S A)⁄(localization S)]
 - but we need `is_pushout R (localization S) A (localized_module S A)` to call this
 -/
theorem kaehler_commutes_wih_localization : (localized_module S Ω[A⁄B]) ≃ₗ[B] Ω[localized_module S A ⁄localization S] :=
begin
  admit
end


end kaehler
#check kaehler_differential.derivation_tensor_product_equiv

