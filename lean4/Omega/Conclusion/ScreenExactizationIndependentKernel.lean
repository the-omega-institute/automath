import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Admissible exactization completions live outside the prescribed partial screen `S0`. -/
def screenExactizationAdmissible (S0 T : Finset V) : Prop :=
  Disjoint T S0

/-- Exactizing `base` with an admissible completion `T` means reaching the target rank `ρ`. -/
def screenExactizationFeasible (ρ : ℕ) (r : Finset V → ℕ) (base S0 T : Finset V) : Prop :=
  screenExactizationAdmissible S0 T ∧ r (base ∪ T) = ρ

/-- Finite list of all admissible exactization completions reaching rank `ρ`. -/
def screenExactizationFeasibleCompletions (ρ : ℕ) (r : Finset V → ℕ) (base S0 : Finset V) :
    Finset (Finset V) :=
  by
    classical
    exact
      (((Finset.univ : Finset V).powerset).filter fun T => screenExactizationAdmissible S0 T).filter
        fun T => r (base ∪ T) = ρ

/-- Additive completion cost attached to a weight function. -/
def screenCompletionCost (c : V → ℕ) (T : Finset V) : ℕ :=
  T.sum c

/-- Minimum completion cost over all feasible completions, with value `0` when none exist. -/
def screenExactizationMinCost (ρ : ℕ) (r : Finset V → ℕ) (base S0 : Finset V) (c : V → ℕ) : ℕ :=
  if h : (screenExactizationFeasibleCompletions ρ r base S0).Nonempty then
    (screenExactizationFeasibleCompletions ρ r base S0).inf' h (screenCompletionCost c)
  else
    0

/-- The partial screen `S0` and its independent kernel `I0` admit the same feasible completions. -/
def screenExactizationSameFeasibleCompletions (ρ : ℕ) (r : Finset V → ℕ) (S0 I0 : Finset V) :
    Prop :=
  ∀ T : Finset V, screenExactizationAdmissible S0 T → (r (S0 ∪ T) = ρ ↔ r (I0 ∪ T) = ρ)

/-- Weighted exactization over `S0` agrees with the corresponding contraction-basis minimization
over `I0` when the feasible completion family is the same. -/
def weightedCompletionCost_eq_contractedBasisCost (ρ : ℕ) (r : Finset V → ℕ)
    (S0 I0 : Finset V) (c : V → ℕ) : Prop :=
  screenExactizationMinCost ρ r S0 S0 c = screenExactizationMinCost ρ r I0 S0 c

/-- In the unweighted case, the minimum feasible completion size is the residual rank gap. -/
def unweightedCompletionCost_eq_rankGap (ρ : ℕ) (r : Finset V → ℕ) (S0 _I0 : Finset V) : Prop :=
  screenExactizationMinCost ρ r S0 S0 (fun _ => 1) = ρ - r S0

lemma mem_screenExactizationFeasibleCompletions (ρ : ℕ) (r : Finset V → ℕ) (base S0 T : Finset V) :
    T ∈ screenExactizationFeasibleCompletions ρ r base S0 ↔
      screenExactizationFeasible ρ r base S0 T := by
  simp [screenExactizationFeasibleCompletions, screenExactizationFeasible,
    screenExactizationAdmissible]

lemma screenExactizationFeasibleCompletions_eq (ρ : ℕ) (r : Finset V → ℕ) (S0 I0 : Finset V)
    (hsame : ∀ T : Finset V, screenExactizationAdmissible S0 T → r (S0 ∪ T) = r (I0 ∪ T)) :
    screenExactizationFeasibleCompletions ρ r S0 S0 =
      screenExactizationFeasibleCompletions ρ r I0 S0 := by
  ext T
  rw [mem_screenExactizationFeasibleCompletions, mem_screenExactizationFeasibleCompletions]
  constructor
  · rintro ⟨hT, hρ⟩
    exact ⟨hT, by rwa [hsame T hT] at hρ⟩
  · rintro ⟨hT, hρ⟩
    exact ⟨hT, by rwa [hsame T hT]⟩

/-- Paper label: `thm:conclusion-screen-exactization-independent-kernel`. -/
theorem paper_conclusion_screen_exactization_independent_kernel
    (ρ : ℕ) (r : Finset V → ℕ) (S0 I0 : Finset V) (c : V → ℕ)
    (hsame : ∀ T : Finset V, screenExactizationAdmissible S0 T → r (S0 ∪ T) = r (I0 ∪ T))
    (hrank : r I0 = r S0)
    (hex :
      ∃ T0 : Finset V,
        screenExactizationAdmissible S0 T0 ∧
          r (I0 ∪ T0) = ρ ∧
            T0.card = ρ - r I0)
    (hlb :
      ∀ T : Finset V,
        screenExactizationAdmissible S0 T → r (I0 ∪ T) = ρ → ρ - r I0 ≤ T.card) :
    screenExactizationSameFeasibleCompletions ρ r S0 I0 ∧
      weightedCompletionCost_eq_contractedBasisCost ρ r S0 I0 c ∧
      unweightedCompletionCost_eq_rankGap ρ r S0 I0 := by
  have hfeq :
      screenExactizationFeasibleCompletions ρ r S0 S0 =
        screenExactizationFeasibleCompletions ρ r I0 S0 :=
    screenExactizationFeasibleCompletions_eq ρ r S0 I0 hsame
  have hcostEq :
      screenExactizationMinCost ρ r S0 S0 c = screenExactizationMinCost ρ r I0 S0 c := by
    unfold screenExactizationMinCost
    simp [hfeq]
  refine ⟨?_, hcostEq, ?_⟩
  · intro T hT
    exact by rw [hsame T hT]
  · obtain ⟨T0, hT0adm, hT0ρ, hT0card⟩ := hex
    let F : Finset (Finset V) := screenExactizationFeasibleCompletions ρ r I0 S0
    have hT0mem : T0 ∈ F := by
      rw [mem_screenExactizationFeasibleCompletions]
      exact ⟨hT0adm, hT0ρ⟩
    have hFne : F.Nonempty := ⟨T0, hT0mem⟩
    have hupper :
        screenExactizationMinCost ρ r I0 S0 (fun _ => 1) ≤ ρ - r I0 := by
      unfold screenExactizationMinCost
      simp [F, hFne]
      simpa [screenCompletionCost, hT0card] using
        (Finset.inf'_le (s := F) (f := screenCompletionCost fun _ : V => 1) hT0mem)
    have hlower' :
        ρ - r I0 ≤ screenExactizationMinCost ρ r I0 S0 (fun _ => 1) := by
      have hFbound :
          ρ - r I0 ≤ F.inf' hFne (screenCompletionCost fun _ : V => 1) := by
        exact Finset.le_inf' (s := F) (H := hFne) (f := screenCompletionCost fun _ : V => 1)
          (a := ρ - r I0) (by
            intro T hT
            rw [mem_screenExactizationFeasibleCompletions] at hT
            rcases hT with ⟨hTadm, hTρ⟩
            have hcard : ρ - r I0 ≤ T.card := hlb T hTadm hTρ
            simpa [screenCompletionCost] using hcard)
      have hminEq :
          screenExactizationMinCost ρ r I0 S0 (fun _ => 1) =
            F.inf' hFne (screenCompletionCost fun _ : V => 1) := by
        unfold screenExactizationMinCost
        simp [F, hFne]
      rw [hminEq]
      exact hFbound
    have hcontract :
        screenExactizationMinCost ρ r I0 S0 (fun _ => 1) = ρ - r I0 :=
      le_antisymm hupper hlower'
    have hscreen :
        screenExactizationMinCost ρ r S0 S0 (fun _ => 1) = ρ - r I0 := by
      have hcostEqOne :
          screenExactizationMinCost ρ r S0 S0 (fun _ => 1) =
            screenExactizationMinCost ρ r I0 S0 (fun _ => 1) := by
        unfold screenExactizationMinCost
        simp [hfeq]
      rw [hcostEqOne, hcontract]
    unfold unweightedCompletionCost_eq_rankGap
    simpa [hrank] using hscreen

end

end Omega.Conclusion
