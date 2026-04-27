import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The audited nominal mode count `N_q = 2 * floor(q / 2) + 1`. -/
def killo_fold_resonance_gap_simple_module_nominalCount (q : ℕ) : ℕ :=
  2 * (q / 2) + 1

/-- The audited minimal characteristic degrees for the resonance window `q = 13, ..., 17`. -/
def killo_fold_resonance_gap_simple_module_degree (q : ℕ) : ℕ :=
  match q with
  | 13 => 11
  | 14 => 13
  | 15 => 11
  | 16 => 13
  | 17 => 13
  | _ => 0

/-- The finite resonance gap table entry `Delta(q) = N_q - d_q`. -/
def killo_fold_resonance_gap_simple_module_delta (q : ℕ) : ℕ :=
  killo_fold_resonance_gap_simple_module_nominalCount q -
    killo_fold_resonance_gap_simple_module_degree q

/-- The q-window audited in the theorem. -/
def killo_fold_resonance_gap_simple_module_window : Finset ℕ :=
  {13, 14, 15, 16, 17}

/-- A direct-sum obstruction for a module identified with a field quotient. -/
def killo_fold_resonance_gap_simple_module_noInvariantDirectSum
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] : Prop :=
  ∀ U V : Submodule K M,
    U ⊔ V = ⊤ → U ⊓ V = ⊥ →
      (U = ⊥ ∧ V = ⊤) ∨ (U = ⊤ ∧ V = ⊥)

/-- Concrete package for the resonance-gap table and the simple-module obstruction. -/
def killo_fold_resonance_gap_simple_module_statement : Prop :=
  killo_fold_resonance_gap_simple_module_delta 13 = 2 ∧
    killo_fold_resonance_gap_simple_module_delta 14 = 2 ∧
    killo_fold_resonance_gap_simple_module_delta 15 = 4 ∧
    killo_fold_resonance_gap_simple_module_delta 16 = 4 ∧
    killo_fold_resonance_gap_simple_module_delta 17 = 4 ∧
    (∀ q : ℕ,
      q ∈ killo_fold_resonance_gap_simple_module_window →
        0 < killo_fold_resonance_gap_simple_module_delta q) ∧
    (∀ (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M],
      Nonempty (M ≃ₗ[K] K) →
        IsSimpleModule K M ∧
          killo_fold_resonance_gap_simple_module_noInvariantDirectSum K M)

/-- Paper label: `thm:killo-fold-resonance-gap-simple-module`. -/
theorem paper_killo_fold_resonance_gap_simple_module :
    killo_fold_resonance_gap_simple_module_statement := by
  refine ⟨by norm_num [killo_fold_resonance_gap_simple_module_delta,
      killo_fold_resonance_gap_simple_module_nominalCount,
      killo_fold_resonance_gap_simple_module_degree],
    by norm_num [killo_fold_resonance_gap_simple_module_delta,
      killo_fold_resonance_gap_simple_module_nominalCount,
      killo_fold_resonance_gap_simple_module_degree],
    by norm_num [killo_fold_resonance_gap_simple_module_delta,
      killo_fold_resonance_gap_simple_module_nominalCount,
      killo_fold_resonance_gap_simple_module_degree],
    by norm_num [killo_fold_resonance_gap_simple_module_delta,
      killo_fold_resonance_gap_simple_module_nominalCount,
      killo_fold_resonance_gap_simple_module_degree],
    by norm_num [killo_fold_resonance_gap_simple_module_delta,
      killo_fold_resonance_gap_simple_module_nominalCount,
      killo_fold_resonance_gap_simple_module_degree],
    ?_, ?_⟩
  · intro q hq
    fin_cases hq <;>
      norm_num [killo_fold_resonance_gap_simple_module_delta,
        killo_fold_resonance_gap_simple_module_nominalCount,
        killo_fold_resonance_gap_simple_module_degree]
  · intro K M _ _ _ hfieldModel
    rcases hfieldModel with ⟨e⟩
    have hsimple : IsSimpleModule K M := IsSimpleModule.congr e
    refine ⟨hsimple, ?_⟩
    intro U V hsup hinf
    haveI : IsSimpleModule K M := hsimple
    rcases eq_bot_or_eq_top U with rfl | rfl
    · left
      constructor
      · rfl
      · simpa using hsup
    · right
      constructor
      · rfl
      · simpa using hinf

end Omega.Folding
