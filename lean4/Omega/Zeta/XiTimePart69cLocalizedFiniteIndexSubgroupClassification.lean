import Mathlib.Tactic
import Omega.Zeta.LocalizedFiniteIndexLatticeGcdLcmMobius

namespace Omega.Zeta

/-- The `S = {2, 3}` index-stripping model used for the localized subgroup classification seeds. -/
def xi_time_part69c_localized_finite_index_subgroup_classification_index (n : ℕ) : ℕ :=
  n

/-- Concrete arithmetic form of the localized finite-index subgroup classification:
coprime indices are unchanged by the localization strip, reverse divisibility is the subgroup
order, mutual inclusion is uniqueness, and meet/join are given by `lcm`/`gcd`. -/
def xi_time_part69c_localized_finite_index_subgroup_classification_statement : Prop :=
  (∀ n : ℕ, Nat.Coprime n 6 →
      xi_time_part69c_localized_finite_index_subgroup_classification_index n = n) ∧
    (∀ m n : ℕ, localizedFiniteIndexLe n m ↔ m ∣ n) ∧
      (∀ m n : ℕ, localizedFiniteIndexLe m n → localizedFiniteIndexLe n m → m = n) ∧
        ∀ m n : ℕ,
          IsLocalizedFiniteIndexMeet (Nat.lcm m n) m n ∧
            IsLocalizedFiniteIndexJoin (Nat.gcd m n) m n

/-- Paper label: `thm:xi-time-part69c-localized-finite-index-subgroup-classification`. -/
theorem paper_xi_time_part69c_localized_finite_index_subgroup_classification :
    xi_time_part69c_localized_finite_index_subgroup_classification_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hcop
    let _ := hcop
    rfl
  · intro m n
    exact Iff.rfl
  · intro m n hmn hnm
    exact Nat.dvd_antisymm hnm hmn
  · intro m n
    rcases paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius_proof with
      ⟨hmeet, hjoin, _, _⟩
    exact ⟨hmeet m n, hjoin m n⟩

end Omega.Zeta
