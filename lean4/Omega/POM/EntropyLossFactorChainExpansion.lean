import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace _root_.List

/-- Compatibility definition for the deprecated `List.enum`, returning index-element pairs. -/
def enum {α : Type*} : List α → List (ℕ × α)
  | [] => []
  | x :: xs => (0, x) :: (enum xs).map (fun ⟨j, y⟩ => (j + 1, y))

lemma enum_nil {α : Type*} : List.enum ([] : List α) = [] := rfl

lemma enum_cons {α : Type*} (x : α) (xs : List α) :
    List.enum (x :: xs) = (0, x) :: ((List.enum xs).map fun ⟨j, y⟩ => (j + 1, y)) := rfl

end List

namespace Omega.POM

/-- The multiplicative entropy-loss cocycle attached to a pressure profile `P`. -/
def pomEntropyLossHelper (P : ℕ → ℝ) (a b : ℕ) : ℝ :=
  (b : ℝ) * P a - P (a * b)

lemma pomEntropyLossHelper_mul (P : ℕ → ℝ) (a b c : ℕ) :
    pomEntropyLossHelper P a (b * c) =
      (c : ℝ) * pomEntropyLossHelper P a b + pomEntropyLossHelper P (a * b) c := by
  unfold pomEntropyLossHelper
  rw [Nat.mul_assoc]
  norm_num [Nat.cast_mul]
  ring

/-- Recursive factor-chain expansion terms for the entropy-loss cocycle. -/
def pomEntropyLossChainTerms (P : ℕ → ℝ) (a : ℕ) : List ℕ → List ℝ
  | [] => []
  | r :: rs => ((rs.prod : ℝ) * pomEntropyLossHelper P a r) :: pomEntropyLossChainTerms P (a * r) rs

lemma pomEntropyLossChainTerms_sum (P : ℕ → ℝ) (a : ℕ) :
    ∀ rs : List ℕ, pomEntropyLossHelper P a rs.prod = (pomEntropyLossChainTerms P a rs).sum
  | [] => by simp [pomEntropyLossHelper, pomEntropyLossChainTerms]
  | r :: rs => by
      rw [List.prod_cons, pomEntropyLossHelper_mul, pomEntropyLossChainTerms]
      simp [pomEntropyLossChainTerms_sum]

lemma pomEntropyLossChainTerms_eq_enumMap (P : ℕ → ℝ) (a : ℕ) :
    ∀ rs : List ℕ,
      pomEntropyLossChainTerms P a rs =
        ((List.enum rs).map fun ⟨j, r⟩ =>
          (((rs.drop (j + 1)).prod : ℝ) * pomEntropyLossHelper P (a * (rs.take j).prod) r))
  | [] => by simp [pomEntropyLossChainTerms, List.enum_nil]
  | r :: rs => by
      simp only [pomEntropyLossChainTerms]
      rw [List.enum_cons]
      simp [pomEntropyLossChainTerms_eq_enumMap, mul_assoc]

/-- Iterating the two-factor cocycle identity expands the entropy loss along any ordered factor
chain.
    cor:pom-entropy-loss-factor-chain-expansion -/
theorem paper_pom_entropy_loss_factor_chain_expansion (P : ℕ → ℝ) :
    let H : ℕ → ℕ → ℝ := fun a b => (b : ℝ) * P a - P (a * b)
    ∀ (a : ℕ) (rs : List ℕ),
      H a rs.prod =
        (((List.enum rs).map fun ⟨j, r⟩ =>
          (((rs.drop (j + 1)).prod : ℝ) * H (a * (rs.take j).prod) r))).sum := by
  dsimp
  intro a rs
  change pomEntropyLossHelper P a rs.prod =
    (((List.enum rs).map fun ⟨j, r⟩ =>
      (((rs.drop (j + 1)).prod : ℝ) * pomEntropyLossHelper P (a * (rs.take j).prod) r))).sum
  simpa [pomEntropyLossChainTerms_eq_enumMap] using pomEntropyLossChainTerms_sum P a rs

end Omega.POM
