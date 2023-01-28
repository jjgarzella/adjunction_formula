import ring_theory.derivation
import algebra.module.localized_module
import ring_theory.localization.basic

section kaehler
noncomputable theory
variables (A B : Type*) [comm_ring A] [comm_ring B] [algebra B A] (S : submonoid B)

def localized_module.algebra_hom : A →ₐ[B] localized_module S A :=
 alg_hom.of_linear_map (localized_module.mk_linear_map S A)
 begin
  rw [localized_module.mk_linear_map_apply],
  refl,
end
begin
  intros,
  iterate 3 { rw [localized_module.mk_linear_map_apply] },
  rw [localized_module.mk_mul_mk, one_mul],
end

instance localized_module.algebra'' : algebra A (localized_module S A) :=
  ring_hom.to_algebra (alg_hom.to_ring_hom (localized_module.algebra_hom A B S))

instance localized_module.is_scalar_tower' : is_scalar_tower B A (localized_module S A) :=
{ smul_assoc := by simp only [smul_assoc, eq_self_iff_true, forall_const] }
instance localized_module.is_pushout :
    algebra.is_pushout B (localization S) A (localized_module S A) :=
begin
  rw algebra.is_pushout_iff,
  convert is_localized_module.is_base_change S (localized_module.mk_linear_map S A),
end

/-
 - Outline:
 - since localization is a tensor product:
 - (localized_module S Ω[A⁄B]) ≃ₗ[B] ((localization S) ⊗[B] Ω[A⁄B])
 -
 - kaehler_differential.derivation_tensor_product_equiv:
 - ((localization S) ⊗[B] Ω[A⁄B]) ≃ₗ[B] Ω[(localized_module S A)⁄(localization S)]
 - but we need `is_pushout R (localization S) A (localized_module S A)` to call this
 -/
theorem kaehler_commutes_wih_localization :
    (localized_module S Ω[A⁄B]) ≃ₗ[B] Ω[localized_module S A ⁄localization S] :=
begin
  have tprod_eq_rhs := kaehler_differential.derivation_tensor_product_equiv B (localization S) A
      (localized_module S A),
  suffices lhs_eq_tprod :
      (localized_module S Ω[A⁄B]) ≃ₗ[localization S] (tensor_product B (localization S) Ω[A ⁄ B]),
  {
    exact linear_equiv.restrict_scalars B (linear_equiv.trans lhs_eq_tprod tprod_eq_rhs),
  },
  have := is_localized_module.is_base_change S (localized_module.mk_linear_map S Ω[A⁄B]),
  exact (is_base_change.equiv this).symm,
end
end kaehler
