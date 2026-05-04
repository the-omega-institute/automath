import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-rank data for the window-6 odd-sector washout certificate. -/
structure conclusion_window6_gaussian_compatible_odd_decoupling_data where
  hiddenOddRank : ℕ
  visibleOddRank : ℕ

namespace conclusion_window6_gaussian_compatible_odd_decoupling_data

def visibleCartanRank
    (_D : conclusion_window6_gaussian_compatible_odd_decoupling_data) : ℕ :=
  1

def hidden_washout
    (D : conclusion_window6_gaussian_compatible_odd_decoupling_data) : Prop :=
  D.hiddenOddRank = 0

def odd_sector_splits
    (D : conclusion_window6_gaussian_compatible_odd_decoupling_data) : Prop :=
  D.hiddenOddRank + D.visibleOddRank = D.visibleOddRank

def no_second_odd_mode
    (D : conclusion_window6_gaussian_compatible_odd_decoupling_data) : Prop :=
  D.hiddenOddRank = 0

def rank_one_cartan_survives
    (D : conclusion_window6_gaussian_compatible_odd_decoupling_data) : Prop :=
  D.visibleCartanRank = 1

end conclusion_window6_gaussian_compatible_odd_decoupling_data

/-- Paper label: `cor:conclusion-window6-gaussian-compatible-odd-decoupling`. -/
theorem paper_conclusion_window6_gaussian_compatible_odd_decoupling
    (D : conclusion_window6_gaussian_compatible_odd_decoupling_data) :
    D.hidden_washout → D.odd_sector_splits ∧ D.no_second_odd_mode ∧
      D.rank_one_cartan_survives := by
  intro hwashout
  unfold conclusion_window6_gaussian_compatible_odd_decoupling_data.hidden_washout at hwashout
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_window6_gaussian_compatible_odd_decoupling_data.odd_sector_splits
    rw [hwashout]
    simp
  · exact hwashout
  · simp [
      conclusion_window6_gaussian_compatible_odd_decoupling_data.rank_one_cartan_survives,
      conclusion_window6_gaussian_compatible_odd_decoupling_data.visibleCartanRank]

end Omega.Conclusion
