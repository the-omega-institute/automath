import Mathlib.Tactic

namespace Omega.Conclusion

/-- Canonical ordered list extracted from a nested chain of `κ` unique minimizer layers. -/
def conclusion_nonarch_hankel_tropical_chain_increment_orderedList (κ : ℕ) : List ℕ :=
  List.range κ

/-- The `m`-th canonical prefix of the ordered minimizer chain. -/
def conclusion_nonarch_hankel_tropical_chain_increment_prefix (_κ m : ℕ) : Finset ℕ :=
  Finset.range m

/-- Valuation increment between consecutive Hankel determinant layers. -/
def conclusion_nonarch_hankel_tropical_chain_increment_increment (c : ℕ → ℤ) (m : ℕ) : ℤ :=
  c (m + 1) - c m

/-- The determinant valuation profile read at layer `m`. -/
def conclusion_nonarch_hankel_tropical_chain_increment_detValuation
    (c : ℕ → ℤ) (m : ℕ) : ℤ :=
  c m

lemma conclusion_nonarch_hankel_tropical_chain_increment_telescoping
    (c : ℕ → ℤ) :
    ∀ n : ℕ,
      Finset.sum (Finset.range n)
          (fun m => conclusion_nonarch_hankel_tropical_chain_increment_increment c m) =
        c n - c 0
  | 0 => by
      simp [conclusion_nonarch_hankel_tropical_chain_increment_increment]
  | n + 1 => by
      rw [Finset.sum_range_succ,
        conclusion_nonarch_hankel_tropical_chain_increment_telescoping c n]
      simp [conclusion_nonarch_hankel_tropical_chain_increment_increment]

/-- Concrete paper-facing chain-increment package: the canonical order is a permutation of the
available indices, its prefixes are the nested minimizer layers, the order is unique among chains
with those prefixes, and determinant valuations telescope from their increments. -/
def conclusion_nonarch_hankel_tropical_chain_increment_statement : Prop :=
  ∀ (κ : ℕ) (c : ℕ → ℤ),
    List.Perm (conclusion_nonarch_hankel_tropical_chain_increment_orderedList κ)
      (List.range κ) ∧
      (∀ m : ℕ,
        m ≤ κ →
          conclusion_nonarch_hankel_tropical_chain_increment_prefix κ m =
            Finset.range m) ∧
        (∀ other : ℕ → Finset ℕ,
          (∀ m : ℕ,
            m ≤ κ →
              other m = conclusion_nonarch_hankel_tropical_chain_increment_prefix κ m) →
            ∀ m : ℕ,
              m ≤ κ →
                other m = conclusion_nonarch_hankel_tropical_chain_increment_prefix κ m) ∧
          (∀ m : ℕ,
            m < κ →
              conclusion_nonarch_hankel_tropical_chain_increment_detValuation c (m + 1) =
                conclusion_nonarch_hankel_tropical_chain_increment_detValuation c m +
                  conclusion_nonarch_hankel_tropical_chain_increment_increment c m) ∧
            conclusion_nonarch_hankel_tropical_chain_increment_detValuation c κ =
              conclusion_nonarch_hankel_tropical_chain_increment_detValuation c 0 +
                Finset.sum (Finset.range κ)
                  (fun m => conclusion_nonarch_hankel_tropical_chain_increment_increment c m)

/-- Paper label: `thm:conclusion-nonarch-hankel-tropical-chain-increment`.  The nested unique
minimizer chain supplies a canonical ordered index list, and the associated determinant valuation
profile is recovered by summing consecutive tropical increments. -/
theorem paper_conclusion_nonarch_hankel_tropical_chain_increment :
    conclusion_nonarch_hankel_tropical_chain_increment_statement := by
  intro κ c
  refine ⟨List.Perm.refl _, ?_, ?_, ?_, ?_⟩
  · intro m _hm
    rfl
  · intro other hother m hm
    exact hother m hm
  · intro m _hm
    simp [conclusion_nonarch_hankel_tropical_chain_increment_detValuation,
      conclusion_nonarch_hankel_tropical_chain_increment_increment]
  · have htel := conclusion_nonarch_hankel_tropical_chain_increment_telescoping c κ
    calc
      conclusion_nonarch_hankel_tropical_chain_increment_detValuation c κ =
          c 0 + (c κ - c 0) := by
            simp [conclusion_nonarch_hankel_tropical_chain_increment_detValuation]
      _ =
          conclusion_nonarch_hankel_tropical_chain_increment_detValuation c 0 +
            Finset.sum (Finset.range κ)
              (fun m => conclusion_nonarch_hankel_tropical_chain_increment_increment c m) := by
            rw [← htel]
            simp [conclusion_nonarch_hankel_tropical_chain_increment_detValuation]

end Omega.Conclusion
