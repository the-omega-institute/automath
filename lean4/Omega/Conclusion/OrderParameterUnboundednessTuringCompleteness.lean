import Mathlib.Tactic
import Omega.POM.FractranFiniteUpdateTableOneStep

namespace Omega.Conclusion

open Omega.POM

/-- The available order parameters are unbounded. -/
def ParamUnbd (B : Set ℕ) : Prop :=
  ∀ K : ℕ, ∃ b ∈ B, K ≤ b

/-- A threshold budget `k` is first-fit universal when it can realize every finite update table
whose state space has size at most `k`. -/
def FirstfitScanRealizable (k : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X], Fintype.card X ≤ k →
    ∀ f : X → X,
      ∃ F : FracPPBotProgram X, fracPPBotProgramToPartialMap F = fun x => some (f x)

/-- The library is first-fit universal when every target table size is admitted by some available
order parameter. -/
def FirstfitUniversal (B : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ b ∈ B, k ≤ b ∧ FirstfitScanRealizable k

/-- Semantic Turing completeness is modeled here by the ability to realize every finite update
table with some available order parameter from `B`. -/
def SemanticTuringComplete (B : Set ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (f : X → X),
    ∃ b ∈ B, Fintype.card X ≤ b ∧
      ∃ F : FracPPBotProgram X, fracPPBotProgramToPartialMap F = fun x => some (f x)

/-- If all available thresholds are bounded by one constant, the order-gate library collapses to a
bounded fragment. -/
def BoundedThresholdCollapse (B : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ b ∈ B, b ≤ C

private lemma firstfitScanRealizable_all (k : ℕ) : FirstfitScanRealizable k := by
  intro X _ _ _ f
  exact paper_pom_fractran_finite_update_table_one_step X f

private lemma paramUnbd_implies_firstfitUniversal {B : Set ℕ} (hB : ParamUnbd B) :
    FirstfitUniversal B := by
  intro k
  rcases hB k with ⟨b, hbB, hkb⟩
  exact ⟨b, hbB, hkb, firstfitScanRealizable_all k⟩

private lemma firstfitUniversal_implies_paramUnbd {B : Set ℕ} (hB : FirstfitUniversal B) :
    ParamUnbd B := by
  intro k
  rcases hB k with ⟨b, hbB, hkb, _⟩
  exact ⟨b, hbB, hkb⟩

private lemma semanticTuringComplete_of_paramUnbd {B : Set ℕ} (hB : ParamUnbd B) :
    SemanticTuringComplete B := by
  intro X _ _ f
  rcases hB (Fintype.card X) with ⟨b, hbB, hcard⟩
  rcases paper_pom_fractran_finite_update_table_one_step X f with ⟨F, hF⟩
  exact ⟨b, hbB, hcard, F, hF⟩

private lemma boundedThresholdCollapse_of_not_paramUnbd {B : Set ℕ} (hB : ¬ ParamUnbd B) :
    BoundedThresholdCollapse B := by
  classical
  rcases not_forall.mp hB with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro b hbB
  have hnot : ¬ K ≤ b := by
    intro hKb
    exact hK ⟨b, hbB, hKb⟩
  exact le_of_lt (Nat.lt_of_not_ge hnot)

private lemma not_semanticTuringComplete_of_boundedThresholdCollapse {B : Set ℕ}
    (hB : BoundedThresholdCollapse B) : ¬ SemanticTuringComplete B := by
  rcases hB with ⟨C, hC⟩
  intro hSem
  rcases hSem (Fin (C + 1)) (fun x => x) with ⟨b, hbB, hcard, _, _⟩
  have hb_le : b ≤ C := hC b hbB
  simp at hcard
  omega

private lemma paramUnbd_of_semanticTuringComplete {B : Set ℕ} (hB : SemanticTuringComplete B) :
    ParamUnbd B := by
  by_contra hUnbd
  exact not_semanticTuringComplete_of_boundedThresholdCollapse
    (boundedThresholdCollapse_of_not_paramUnbd hUnbd) hB

/-- Unbounded order parameters are exactly the first-fit-universal libraries, and this is also the
same condition as semantic Turing completeness in the concrete finite-update-table model.
    thm:conclusion-order-parameter-unboundedness-turing-completeness -/
theorem paper_conclusion_order_parameter_unboundedness_turing_completeness (B : Set ℕ) :
    (SemanticTuringComplete B ↔ ParamUnbd B) ∧ (ParamUnbd B ↔ FirstfitUniversal B) := by
  refine ⟨?_, ?_⟩
  · exact ⟨paramUnbd_of_semanticTuringComplete, semanticTuringComplete_of_paramUnbd⟩
  · exact ⟨paramUnbd_implies_firstfitUniversal, firstfitUniversal_implies_paramUnbd⟩

end Omega.Conclusion
