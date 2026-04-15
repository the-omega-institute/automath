import Mathlib.Data.List.Nodup
import Omega.EA.PrimeRegisterMultiplicativeNormalizationAdditiveIso
import Omega.EA.RewriteTermination

namespace Omega.EA

open Omega.Rewrite

local instance : IsTrans Nat (fun a b ↦ b + 2 ≤ a) where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

local instance : Std.Irrefl (fun a b : Nat ↦ b + 2 ≤ a) where
  irrefl a h := by
    omega

private theorem registerOfIndices_apply_eq_count :
    ∀ {l : List Nat}, l.IsZeckendorfRep → ∀ k : Nat,
      registerOfIndices l k = l.count (k + 2)
  | [], _hRep, k => by
      simp [registerOfIndices]
  | a :: l, hRep, k => by
      have hk : 2 ≤ a := X.two_le_of_mem_isZeckendorfRep hRep (by simp)
      have hTail : l.IsZeckendorfRep := X.isZeckendorfRep_tail hRep
      by_cases hEq : a = k + 2
      · subst hEq
        simp [registerOfIndices, registerOfIndices_apply_eq_count hTail, Nat.add_comm]
      · have hNe : a - 2 ≠ k := by
          omega
        simp [registerOfIndices, registerOfIndices_apply_eq_count hTail, hEq, hNe]

private theorem zeckendorf_nodup :
    ∀ {l : List Nat}, l.IsZeckendorfRep → l.Nodup
  | [], _hRep => by
      simp
  | a :: l, hRep => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (a :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using hRep
      have hTail : l.IsZeckendorfRep := X.isZeckendorfRep_tail hRep
      refine List.nodup_cons.mpr ?_
      constructor
      · intro ha
        have hMem : a ∈ l ++ [0] := List.mem_append_left [0] ha
        have hRel : a + 2 ≤ a := hChain.rel_cons hMem
        omega
      · exact zeckendorf_nodup hTail

private theorem registerOfIndices_mem_iff {l : List Nat} (hRep : l.IsZeckendorfRep) (k : Nat) :
    0 < registerOfIndices l k ↔ k + 2 ∈ l := by
  rw [registerOfIndices_apply_eq_count hRep]
  simpa using List.count_pos_iff_mem

private theorem registerOfIndices_stable {l : List Nat} (hRep : l.IsZeckendorfRep) :
    StableCfg (registerOfIndices l) := by
  refine ⟨?_, ?_⟩
  · intro k
    rw [registerOfIndices_apply_eq_count hRep]
    exact (List.nodup_iff_count_le_one.mp (zeckendorf_nodup hRep)) (k + 2)
  · intro k hAdj
    have hk : k + 2 ∈ l := (registerOfIndices_mem_iff hRep k).mp hAdj.1
    have hk1 : k + 3 ∈ l := by
      simpa [Nat.add_assoc] using (registerOfIndices_mem_iff hRep (k + 1)).mp hAdj.2
    exact X.not_mem_succ_of_mem_isZeckendorfRep hRep hk hk1

private theorem R_F_irreducible (n : ℕ) : Irreducible (R_F n) := by
  refine irreducible_of_stableCfg ?_
  exact registerOfIndices_stable (Nat.isZeckendorfRep_zeckendorf n)

private theorem NF_pr_irreducible (a : DigitCfg) : Irreducible (NF_pr a) :=
  R_F_irreducible (valPr a)

private theorem NF_pr_reduces (a : DigitCfg) : Relation.ReflTransGen Step a (NF_pr a) := by
  obtain ⟨b, hab, hIrrB⟩ := exists_irreducible_descendant a
  have hVal : valPr b = valPr (NF_pr a) := by
    calc
      valPr b = valPr a := by
        simpa using (reflTransGen_value hab)
      _ = valPr (NF_pr a) := by
        simp [NF_pr]
  have hEq : b = NF_pr a := by
    apply irreducible_eq_of_value_eq hIrrB (NF_pr_irreducible a)
    simpa using hVal
  simpa [hEq] using hab

/-- Paper-facing wrapper: every prime-register state reduces to the canonical register
    `NF_pr`, and that irreducible descendant is unique.
    prop:prime-register-normal-form-uniqueness -/
theorem paper_prime_register_normal_form_uniqueness (a : DigitCfg) :
    Relation.ReflTransGen Step a (NF_pr a) ∧
      Irreducible (NF_pr a) ∧
      ∀ b : DigitCfg, Relation.ReflTransGen Step a b → Irreducible b → b = NF_pr a := by
  refine ⟨NF_pr_reduces a, NF_pr_irreducible a, ?_⟩
  intro b hab hIrrB
  exact irreducible_terminal_unique_unbounded hab (NF_pr_reduces a) hIrrB (NF_pr_irreducible a)

end Omega.EA
