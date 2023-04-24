import ring_theory.nakayama
import ring_theory.jacobson_ideal
import algebra.module.torsion

set_option pp.coercions true
-- set_option pp.implicit true

-- open_locale classical

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open ideal

-- #reduce (⊤ : submodule R M) ⊔ (⊥ : submodule R M)
-- #check @submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot

-- def quot_module_structure (I : ideal R) :
-- module (R ⧸ I) (M ⧸ I • (⊤ : submodule R M))
-- := by apply_instance

-- my unfinished attempt to do a similar proof to nakayama.lean, where
-- --   they have an "ambient module"
-- lemma generate_of_quotient_generate_of_le_jacobson_ambient (I : ideal R) (N : submodule R M)
-- (S : finset M) (hN : N.fg) --submodule.span imageof(S) (quotient N/IN)
-- : (submodule.span R ↑S = N) := sorry

-- lemma in_sup_of_residue_in_quotient (x : M) (N P : submodule R M)
-- (hNP : (submodule.quotient.mk x) ∈ (submodule.map (submodule.mkq P) N)) :
-- (x ∈ N ⊔ P) :=
-- begin
--   sorry,
--   -- let want to apply submodule.quotient.eq to x and 0
--   -- have submodule.comap
--   -- apply [submodule.quotient.eq],
-- end

-- lemma submodule_of_mem (N P : submodule R M) :
-- (N ≤ P ↔ ∀ x, x ∈ N → x ∈ P) :=
-- begin
--   exact set_like.le_def
-- end



-- lemma generate_of_quotient_generate_of_le_jacobson (I : ideal R)
-- (hM : (⊤ : submodule R M).fg) (hIjac : I ≤ jacobson ⊥) (S : finset M)
-- (hIM : submodule.span (R ⧸ I) (submodule.quotient.mk '' ↑S) =
-- (⊤ : submodule (R ⧸ I) (M ⧸ (I • (⊤ : submodule R M)))))
-- : (submodule.span R ↑S = (⊤ : submodule R M)) :=
-- begin
--   let N := (submodule.span R ↑S),
--   let MM := (⊤ : submodule R M),
--   suffices hh : N ⊔ (I • MM) = MM,
--     have htop : N ⊔ MM = MM,
--       by simp only [eq_self_iff_true, sup_top_eq],
--     have hItop : N ⊔ (I • MM) = N ⊔ MM,
--       by exact eq.trans hh htop.symm,
--     have hIineqtop : N ⊔ MM ≤ N ⊔ I • MM,
--       by simp only [eq_self_iff_true, sup_top_eq, hItop, top_le_iff],
--     have blah : I • MM ≤ N,
--       apply submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot hM hIjac hIineqtop,
--     have blah2 : N = N ⊔ (I • MM),
--       by simp [blah],
--     exact eq.trans blah2 hh,
--   have sup_symm : (I • MM) ⊔ N = N ⊔ (I • MM),
--     by exact sup_comm,
--   rw [←sup_symm],
--   rw [←submodule.map_mkq_eq_top (I • MM) N],
--   sorry,
--   -- rw [←hIM],


--   -- have blah3 : MM ≤ N ⊔ (I • MM),
--   --   sorry,
--   --   -- rw [set_like.le_def],
--   --   -- intro x,
--   --   -- suffices : x ∈ N ⊔ I • MM,
--   --   --   by { simp [forall_true_left], exact this },
--   --   -- have quot_in_span : submodule.quotient.mk x ∈ submodule.span (R ⧸ I) (submodule.quotient.mk '' ↑S),
--   --   --   by {
--   --   --     have : submodule.quotient.mk x ∈ (⊤ : submodule (R ⧸ I) (M ⧸ (I • (⊤ : submodule R M)))),
--   --   --       by refine add_subgroup.mem_top (submodule.quotient.mk x),
--   --   --     rw [hIM],
--   --   --     exact this,
--   --   --   },




--   -- have blah4 : N ⊔ (I • MM) ≤ MM,
--   --   simp,
--   -- exact le_antisymm blah4 blah3,
--   -- simp [blah3, blah5],

--      -- apply submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot _ _ _ _ _ _ N (⊤ : submodule R M) hM hIjac hIineqtop,

--   --sorry,
--   --sorry,
-- end


-- All of the following is due to Adam Topaz.

-- import ring_theory.nakayama
-- import ring_theory.jacobson_ideal
-- import algebra.module.torsion

-- set_option pp.coercions true
open_locale big_operators

-- variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

variable (M)
def submodule.mkqₛₗ (I : ideal R) : M →ₛₗ[ideal.quotient.mk I] M ⧸ (I • (⊤ : submodule R M)) :=
{ ..(submodule.mkq _) }

def submodule.idqₛₗ (I : ideal R) : M ⧸ (I • (⊤ : submodule R M)) →ₛₗ[ideal.quotient.mk I]
  M ⧸ (I • (⊤ : submodule R M)) :=
{ ..(linear_map.id : (M ⧸ (I • (⊤ : submodule R M))) →ₗ[R] _) }

@[simps apply]
def foobar (I : ideal R) : submodule R (M ⧸ (I • (⊤ : submodule R M))) ≃o
  submodule (R ⧸ I) (M ⧸ (I • (⊤ : submodule R M))) :=
{ to_fun := λ N, N.map (submodule.idqₛₗ M I),
  inv_fun := λ N, ⟨N, λ _ _, N.add_mem, N.zero_mem, λ c x hx, N.smul_mem ↑c hx⟩,
  left_inv := λ N, by { ext t, change _ ∈ id '' _ ↔ _, simp, },
  right_inv := λ _, by { ext t, change _ ∈ id '' _ ↔ _, simp, },
  map_rel_iff' := begin
    intros a b,
    dsimp,
    let a' : set (M ⧸ (I • (⊤ : submodule R M))) := a,
    let b' : set (M ⧸ (I • (⊤ : submodule R M))) := b,
    change id '' a' ≤ id '' b' ↔ a ≤ b,
    simp,
  end }

lemma foo (I : ideal R) (N : submodule R M) :
  (N.map $ submodule.mkq (I • (⊤ : submodule R M))).map (submodule.idqₛₗ M I) =
  N.map (submodule.mkqₛₗ M I) :=
begin
  apply set_like.coe_injective,
  change id '' _ = _,
  simp,
  refl,
end

open ideal

lemma generate_of_quotient_generate_of_le_jacobson (I : ideal R)
(hM : (⊤ : submodule R M).fg) (hIjac : I ≤ jacobson ⊥) (N : submodule R M)
(hIM : submodule.map (submodule.mkqₛₗ M I) N = ⊤) : N = (⊤ : submodule R M) :=
begin
  let MM : submodule R M := ⊤,
  suffices hh : N ⊔ (I • MM) = MM,
  { have nak : I • MM ≤ N,
    { apply submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot hM hIjac _,
      simpa only [eq_self_iff_true, sup_top_eq, top_le_iff] },
    rw [(show N = N ⊔ (I • MM), by simp [nak]), hh] },
  rw [sup_comm, ← submodule.map_mkq_eq_top (I • MM) N],
  apply_fun foobar _ _,
  rw order_iso.map_top,
  convert hIM,
  dsimp,
  rw foo,
end