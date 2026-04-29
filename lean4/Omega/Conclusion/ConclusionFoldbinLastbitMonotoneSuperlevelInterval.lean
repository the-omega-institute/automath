import Mathlib.Tactic
import Omega.Folding.FoldBinFiberTail

namespace Omega.Conclusion

/-- The Zeckendorf values that occur on the fixed last-bit layer `b`. -/
def conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer
    (m : ℕ) (b : Bool) : Set ℕ :=
  {V | V < Nat.fib (m + 2) ∧ Omega.get (Omega.X.ofNat m V).1 (m - 1) = b}

/-- Tail-feasible bin-fold candidates on the fixed last-bit layer `b` with budget `V`. -/
def conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible
    (m : ℕ) (b : Bool) (V : ℕ) (N : Fin (2 ^ m)) : Prop :=
  Omega.get (Omega.cBinFold m N.1).1 (m - 1) = b ∧
    V + Omega.stableValue (Omega.cBinFold m N.1) ≤ 2 ^ m - 1

/-- Tail multiplicity obtained by counting all feasible tails at budget `V`. -/
noncomputable def conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity
    (m : ℕ) (b : Bool) (V : ℕ) : ℕ :=
  by
    classical
    exact
      (Finset.univ.filter fun N : Fin (2 ^ m) =>
        conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible m b V N).card

/-- Superlevel set of the tail multiplicity profile on the last-bit layer `b`. -/
def conclusion_foldbin_lastbit_monotone_superlevel_interval_superlevel
    (m : ℕ) (b : Bool) (r : ℕ) : Set ℕ :=
  {V |
    V ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b ∧
      r ≤ conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V}

/-- Exact level set of the tail multiplicity profile on the last-bit layer `b`. -/
def conclusion_foldbin_lastbit_monotone_superlevel_interval_exactLevel
    (m : ℕ) (b : Bool) (r : ℕ) : Set ℕ :=
  {V |
    V ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b ∧
      conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V = r}

private theorem conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible_antitone
    {m : ℕ} {b : Bool} {V₁ V₂ : ℕ} (hV : V₁ ≤ V₂) :
    ∀ {N : Fin (2 ^ m)},
      conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible m b V₂ N →
        conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible m b V₁ N := by
  intro N hN
  exact ⟨hN.1, le_trans (Nat.add_le_add_right hV _) hN.2⟩

private theorem conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity_antitone
    (m : ℕ) (b : Bool) {V₁ V₂ : ℕ} (hV : V₁ ≤ V₂) :
    conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V₂ ≤
      conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V₁ := by
  unfold conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity
  refine Finset.card_le_card ?_
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN ⊢
  exact conclusion_foldbin_lastbit_monotone_superlevel_interval_tailFeasible_antitone hV hN

/-- Paper label: `thm:conclusion-foldbin-lastbit-monotone-superlevel-interval`. The already
verified fiber/tail correspondence supplies a concrete tail model on each fixed last-bit layer;
within that model, increasing the Zeckendorf budget can only delete feasible tails, so the
multiplicity profile is antitone and every superlevel set is an initial segment. -/
theorem paper_conclusion_foldbin_lastbit_monotone_superlevel_interval
    (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    (∀ {V : ℕ},
      V ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b →
        Omega.Folding.FoldBinFiberTailSpec m (Omega.X.ofNat m V)) ∧
      (∀ {V₁ V₂ : ℕ},
        V₁ ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b →
          V₂ ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b →
            V₁ ≤ V₂ →
              conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V₂ ≤
                conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V₁) ∧
      (∀ {r V₁ V₂ : ℕ},
        V₂ ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_superlevel m b r →
          V₁ ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_valueLayer m b →
            V₁ ≤ V₂ →
              V₁ ∈ conclusion_foldbin_lastbit_monotone_superlevel_interval_superlevel m b r) ∧
      (∀ r : ℕ,
        conclusion_foldbin_lastbit_monotone_superlevel_interval_exactLevel m b r =
          conclusion_foldbin_lastbit_monotone_superlevel_interval_superlevel m b r \
            conclusion_foldbin_lastbit_monotone_superlevel_interval_superlevel m b (r + 1)) := by
  let _ := hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V hV
    exact Omega.Folding.paper_fold_bin_fiber_tail m (Omega.X.ofNat m V)
  · intro V₁ V₂ _ _ hV
    exact conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity_antitone m b hV
  · intro r V₁ V₂ hV₂ hV₁ hle
    refine ⟨hV₁, ?_⟩
    exact le_trans hV₂.2
      (conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity_antitone m b hle)
  · intro r
    ext V
    constructor
    · intro hV
      refine ⟨⟨hV.1, hV.2 ▸ le_rfl⟩, ?_⟩
      intro hcontra
      have : r + 1 ≤ r := by simpa [hV.2] using hcontra.2
      exact Nat.not_succ_le_self r this
    · intro hV
      refine ⟨hV.1.1, ?_⟩
      have hr : r ≤ conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V :=
        hV.1.2
      have hlt :
          conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V < r + 1 := by
        have hnot :
            ¬ r + 1 ≤
              conclusion_foldbin_lastbit_monotone_superlevel_interval_multiplicity m b V := by
          intro hge
          exact hV.2 ⟨hV.1.1, hge⟩
        exact Nat.lt_of_not_ge hnot
      omega

end Omega.Conclusion
