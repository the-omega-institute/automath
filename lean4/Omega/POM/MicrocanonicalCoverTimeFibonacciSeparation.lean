import Omega.POM.MicrocanonicalCoverTimeNlognScale
import Omega.POM.MicrocanonicalFoldWorstcaseQueryRigidity
import Omega.Folding.CollisionZetaOperator

namespace Omega.POM

/-- The Fibonacci-scale section-acquisition proxy `m · |X_m|`. -/
noncomputable def pom_microcanonical_cover_time_fibonacci_separation_sectionScale (m : ℕ) : ℕ :=
  m * Fintype.card (Omega.X m)

/-- The full-map worst-case identification proxy `2^m - 1`. -/
def pom_microcanonical_cover_time_fibonacci_separation_fullIdentificationScale (m : ℕ) : ℕ :=
  2 ^ m - 1

/-- Concrete statement for
`cor:pom-microcanonical-cover-time-fibonacci-separation`.

It records the verified Fibonacci compression growth/ratio lemmas, the uniform sparse-language
bound `|X_m| < 2^m`, and a concrete even scale where the `m |X_m|` cover-time proxy is
already below the full-identification `2^m - 1` proxy. -/
def pom_microcanonical_cover_time_fibonacci_separation_statement : Prop :=
  (2 ^ 2 > Fintype.card (Omega.X 2) ∧ 2 ^ 4 > Fintype.card (Omega.X 4) ∧
    2 ^ 6 > Fintype.card (Omega.X 6) ∧ 2 ^ 8 > Fintype.card (Omega.X 8) ∧
    2 ^ 10 > Fintype.card (Omega.X 10)) ∧
    (2 ^ 4 / Fintype.card (Omega.X 4) = 2 ∧
      2 ^ 6 / Fintype.card (Omega.X 6) = 3 ∧
      2 ^ 8 / Fintype.card (Omega.X 8) = 4 ∧
      2 ^ 10 / Fintype.card (Omega.X 10) = 7) ∧
    (∀ m : ℕ, 2 ≤ m → Fintype.card (Omega.X m) < 2 ^ m) ∧
    pom_microcanonical_cover_time_fibonacci_separation_sectionScale 14 <
      pom_microcanonical_cover_time_fibonacci_separation_fullIdentificationScale 14 ∧
    pom_microcanonical_cover_time_fibonacci_separation_sectionScale 14 = 13818 ∧
    pom_microcanonical_cover_time_fibonacci_separation_fullIdentificationScale 14 = 16383

/-- Paper label: `cor:pom-microcanonical-cover-time-fibonacci-separation`. -/
theorem paper_pom_microcanonical_cover_time_fibonacci_separation :
    pom_microcanonical_cover_time_fibonacci_separation_statement := by
  refine ⟨Omega.compression_growth, Omega.compression_ratios, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simpa [Omega.X.card_eq_fib] using Omega.stable_language_exponentially_sparse m hm
  · simp [pom_microcanonical_cover_time_fibonacci_separation_sectionScale,
      pom_microcanonical_cover_time_fibonacci_separation_fullIdentificationScale,
      Omega.X.card_eq_fib]
    native_decide
  · simp [pom_microcanonical_cover_time_fibonacci_separation_sectionScale, Omega.X.card_eq_fib]
    native_decide
  · simp [pom_microcanonical_cover_time_fibonacci_separation_fullIdentificationScale]

end Omega.POM
