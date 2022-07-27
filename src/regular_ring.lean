import data.set.basic
import data.quot
import ring_theory.ideal.operations
import ring_theory.ideal.quotient
import linear_algebra.quotient

variables (R M : Type _) [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

/- CURRENT GOAL:
variables [is_noetherian_ring R] [local_ring R]
def m := local_ring.maximal_ideal R
def regular_ring : Prop :=
  module.rank (R ⧸ m) (m ⧸ (m • (⊤ submodule R m))) = μ(m)

but for this need
  (m /m²) to be an R⧸M module
  μ(m) to be defined
-/

instance quotient_over_ideal_smul_residue : has_smul (R ⧸ I) (M ⧸ (I • (⊤ : submodule R M))) :=
⟨ λ r m, @quotient.lift_on₂' _ _ _ (submodule.quotient_rel _) (submodule.quotient_rel _) r m
    (λ (r : R) (m : M), submodule.quotient.mk $ r • m)
  begin
    intros r₁ m₁ r₂ m₂ h₁ h₂,
    unfold,
    rw submodule.quotient.eq,
    have : (r₁ = r₂ + (r₁ - r₂)) := by ring,
    rw this, clear this,
    have : (r₂ + (r₁ - r₂))•m₁ = r₂•m₁ + (r₁ - r₂)•m₁,
    { rw add_smul },
    rw this, clear this,
    have silly_lemma : ∀(a b c : M), a + b - c = (a - c) + b,
    {
      introv,
      repeat { rw add_comm_group.sub_eq_add_neg, },
      rw add_comm_group.add_assoc,
      have : (b + -c) = (-c + b) := add_comm_group.add_comm _ _,
      erw this, clear this,
      rw ← add_comm_group.add_assoc,
      refl
    },
    rw silly_lemma,
    apply (submodule.add_mem (I • (⊤ : submodule R M))),
    {
      have : m₁ = m₂ + (m₁ - m₂),
      {
        simp only [add_sub_cancel'_right, eq_self_iff_true]
      },
      rw [this, smul_add, silly_lemma, add_comm_group.sub_eq_add_neg, add_neg_self, zero_add ],
      clear this,
      apply (submodule.smul_mem' _ _ _),
      rw submodule.quotient_rel_r_def at h₂,
      assumption
    },
    {
      apply submodule.smul_mem_smul,
      {
        rw ← quotient.eq' at h₁,
        rw ← ideal.quotient.eq,
        assumption,
      },
      {
        exact submodule.mem_top,
      },
    },
  end⟩


/-
def quotient_over_ideal_residue_module : module (R ⧸ I) (M ⧸ (I • (⊤ : submodule R M))) :=
{
  one_smul  := sorry,
  mul_smul  := sorry,
  smul_add  := sorry,
  smul_zero := sorry,
  zero_smul := sorry,
  add_smul  := sorry,
}
-/
