import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.SPG

/-- A concrete prime-channel readout on three generators. -/
def hypercubeH1PrimeChannel (i : Fin 3) : ℕ :=
  if i.1 = 0 then 2 else if i.1 = 1 then 3 else 5

lemma hypercubeH1PrimeChannel_injective : Function.Injective hypercubeH1PrimeChannel := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [hypercubeH1PrimeChannel] at hij ⊢

/-- Concrete minimality statement for the three-generator prime budget. -/
def HypercubeH1PrimeBudgetMinimalStatement : Prop :=
  Function.Injective hypercubeH1PrimeChannel ∧
    ∀ k : ℕ, (∃ f : Fin 3 → Fin k, Function.Injective f) → 3 ≤ k

theorem hypercubeH1PrimeBudgetMinimalCertificate :
    HypercubeH1PrimeBudgetMinimalStatement := by
  refine ⟨hypercubeH1PrimeChannel_injective, ?_⟩
  intro k hk
  rcases hk with ⟨f, hf⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Paper label: `prop:fold-hypercube-h1-prime-budget-minimal`. -/
theorem paper_fold_hypercube_h1_prime_budget_minimal :
    HypercubeH1PrimeBudgetMinimalStatement := by
  exact hypercubeH1PrimeBudgetMinimalCertificate

end Omega.SPG
