import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.POM.FiniteAuditNFAnom

namespace Omega.POM

/-- Paper label: `thm:pom-no-computable-sufficient-slice-selector`.
If a total selector chose a finite audit slice for every pair of semantic families and comparing
the conservative finite-signature semantics on that slice were already sufficient for global
algorithmic equivalence, then that finite comparison would decide the family equivalence problem.
Applying the assumed reduction from an undecidable predicate yields a contradiction. -/
theorem paper_pom_no_computable_sufficient_slice_selector
    {Code Slice Sig NF Anom : Type*}
    (embed : Code → Nat → Slice) (ref : Nat → Slice)
    (finiteSignature : Slice → Sig) (SemNF : Slice → NF) (SemAnom : Slice → Anom)
    (iso algEq : Slice → Slice → Prop) (nonHalting : Code → Prop)
    (audit : (Nat → Slice) → (Nat → Slice) → Finset ℕ)
    (hFinite :
      ∀ {w₁ w₂ : Slice}, finiteSignature w₁ = finiteSignature w₂ →
        SemNF w₁ = SemNF w₂ ∧ SemAnom w₁ = SemAnom w₂)
    (hSem :
      ∀ {w₁ w₂ : Slice}, SemNF w₁ = SemNF w₂ → SemAnom w₁ = SemAnom w₂ → algEq w₁ w₂)
    (hIso : ∀ {w₁ w₂ : Slice}, algEq w₁ w₂ → iso w₁ w₂)
    (hAlgEqFinite : ∀ {w₁ w₂ : Slice}, algEq w₁ w₂ → finiteSignature w₁ = finiteSignature w₂)
    (hSufficient :
      ∀ G H : Nat → Slice,
        (∀ m ∈ audit G H, iso (G m) (H m) ∧ algEq (G m) (H m)) →
          ∀ m, algEq (G m) (H m))
    (hReduction : ∀ c, nonHalting c ↔ ∀ m, algEq (embed c m) (ref m))
    (hUndecidable : ¬ Nonempty (∀ c, Decidable (nonHalting c))) :
    ¬ Nonempty (∀ G H : Nat → Slice,
      Decidable (∀ m ∈ audit G H, finiteSignature (G m) = finiteSignature (H m))) := by
  classical
  intro hSliceDecidable
  apply hUndecidable
  refine ⟨?_⟩
  intro c
  let hDec := Classical.choice hSliceDecidable
  letI := hDec (embed c) ref
  have hAuditIff :
      (∀ m ∈ audit (embed c) ref, finiteSignature (embed c m) = finiteSignature (ref m)) ↔
        ∀ m, algEq (embed c m) (ref m) := by
    constructor
    · intro hAudit m
      have hSlice :
          ∀ j ∈ audit (embed c) ref, iso (embed c j) (ref j) ∧ algEq (embed c j) (ref j) := by
        intro j hj
        exact paper_pom_finite_audit_nf_anom finiteSignature SemNF SemAnom iso algEq
          hFinite hSem hIso (hAudit j hj)
      exact hSufficient (embed c) ref hSlice m
    · intro hAlg m hm
      exact hAlgEqFinite (hAlg m)
  exact decidable_of_iff
    (∀ m ∈ audit (embed c) ref, finiteSignature (embed c m) = finiteSignature (ref m))
    ((hReduction c).trans hAuditIff.symm).symm

end Omega.POM
