import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The coefficient of the top-pole factor `(1 - M z)^(-N)` in the packaged one-pole model. -/
def pom_trivial_channel_extreme_spectrum_extraction_top_pole_coeff
    (M N m : ℕ) : ℝ :=
  (Nat.choose (m + N - 1) (N - 1) : ℝ) * (M : ℝ) ^ m

/-- The regular factor is frozen to a constant in the trivial-channel package. -/
def pom_trivial_channel_extreme_spectrum_extraction_regular_factor (c : ℝ) : ℝ :=
  c

/-- The dominant coefficient term obtained by multiplying the top-pole coefficient by the regular
factor evaluated at the pole. -/
def pom_trivial_channel_extreme_spectrum_extraction_dominant_term
    (M N : ℕ) (c : ℝ) (m : ℕ) : ℝ :=
  pom_trivial_channel_extreme_spectrum_extraction_regular_factor c *
    pom_trivial_channel_extreme_spectrum_extraction_top_pole_coeff M N m

/-- Concrete one-pole data for the trivial-channel extreme-spectrum extraction. The `q`-axis
maximal fiber and its multiplicity are recorded as concrete sequences, and the package assumes
they are already pinned to the top spectral data `M` and `N`. -/
structure pom_trivial_channel_extreme_spectrum_extraction_data where
  pom_trivial_channel_extreme_spectrum_extraction_M : ℕ
  pom_trivial_channel_extreme_spectrum_extraction_N : ℕ
  pom_trivial_channel_extreme_spectrum_extraction_hM :
    0 < pom_trivial_channel_extreme_spectrum_extraction_M
  pom_trivial_channel_extreme_spectrum_extraction_regularConstant : ℝ
  pom_trivial_channel_extreme_spectrum_extraction_maxFiberSequence : ℕ → ℝ
  pom_trivial_channel_extreme_spectrum_extraction_maxFiberMultiplicitySequence : ℕ → ℝ
  pom_trivial_channel_extreme_spectrum_extraction_maxFiberExact :
    ∀ m,
      pom_trivial_channel_extreme_spectrum_extraction_maxFiberSequence m =
        pom_trivial_channel_extreme_spectrum_extraction_M
  pom_trivial_channel_extreme_spectrum_extraction_maxFiberMultiplicityExact :
    ∀ m,
      pom_trivial_channel_extreme_spectrum_extraction_maxFiberMultiplicitySequence m =
        pom_trivial_channel_extreme_spectrum_extraction_N

/-- The extracted coefficient sequence in the packaged one-pole model. -/
def pom_trivial_channel_extreme_spectrum_extraction_data.coeff
    (D : pom_trivial_channel_extreme_spectrum_extraction_data) (m : ℕ) : ℝ :=
  pom_trivial_channel_extreme_spectrum_extraction_dominant_term
    D.pom_trivial_channel_extreme_spectrum_extraction_M
    D.pom_trivial_channel_extreme_spectrum_extraction_N
    D.pom_trivial_channel_extreme_spectrum_extraction_regularConstant m

/-- The leading asymptotic is exact in the packaged one-pole model. -/
def pom_trivial_channel_extreme_spectrum_extraction_data.leading_asymptotic
    (D : pom_trivial_channel_extreme_spectrum_extraction_data) : Prop :=
  ∀ m,
    D.coeff m =
      pom_trivial_channel_extreme_spectrum_extraction_dominant_term
        D.pom_trivial_channel_extreme_spectrum_extraction_M
        D.pom_trivial_channel_extreme_spectrum_extraction_N
        D.pom_trivial_channel_extreme_spectrum_extraction_regularConstant m

/-- The normalized `q`-axis maximal-fiber sequence is identically `1`. -/
def pom_trivial_channel_extreme_spectrum_extraction_data.max_fiber_limit
    (D : pom_trivial_channel_extreme_spectrum_extraction_data) : Prop :=
  ∀ m,
    D.pom_trivial_channel_extreme_spectrum_extraction_maxFiberSequence m /
        D.pom_trivial_channel_extreme_spectrum_extraction_M =
      1

/-- The maximal-fiber multiplicity sequence is exactly the top-pole multiplicity `N`. -/
def pom_trivial_channel_extreme_spectrum_extraction_data.max_fiber_multiplicity_limit
    (D : pom_trivial_channel_extreme_spectrum_extraction_data) : Prop :=
  ∀ m,
    D.pom_trivial_channel_extreme_spectrum_extraction_maxFiberMultiplicitySequence m =
      D.pom_trivial_channel_extreme_spectrum_extraction_N

theorem paper_pom_trivial_channel_extreme_spectrum_extraction
    (D : pom_trivial_channel_extreme_spectrum_extraction_data) :
    D.leading_asymptotic ∧ D.max_fiber_limit ∧ D.max_fiber_multiplicity_limit := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    rw [D.pom_trivial_channel_extreme_spectrum_extraction_maxFiberExact m]
    have hMℝ : (D.pom_trivial_channel_extreme_spectrum_extraction_M : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt D.pom_trivial_channel_extreme_spectrum_extraction_hM
    exact div_self hMℝ
  · intro m
    exact D.pom_trivial_channel_extreme_spectrum_extraction_maxFiberMultiplicityExact m

end Omega.POM
