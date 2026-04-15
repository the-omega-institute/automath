import Mathlib.Tactic

namespace Omega.POM.CatalanMoments

/-- Catalan number: C_n = C(2n,n)/(n+1). -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Catalan number seeds and recurrence witnesses.
    cor:pom-Lk-boundary-catalan-moments-gf -/
theorem paper_pom_catalan_moments :
    (1 * catalanNumber 0 = Nat.choose 0 0) ∧
    (2 * catalanNumber 1 = Nat.choose 2 1) ∧
    (3 * catalanNumber 2 = Nat.choose 4 2) ∧
    (4 * catalanNumber 3 = Nat.choose 6 3) ∧
    (5 * catalanNumber 4 = Nat.choose 8 4) ∧
    (6 * catalanNumber 5 = Nat.choose 10 5) ∧
    (catalanNumber 0 = 1) ∧ (catalanNumber 1 = 1) ∧
    (catalanNumber 2 = 2) ∧ (catalanNumber 3 = 5) ∧
    (catalanNumber 4 = 14) ∧ (catalanNumber 5 = 42) ∧
    (1 * 2 + 1 * 1 + 2 * 1 = 5) ∧
    (1 * 5 + 1 * 2 + 2 * 1 + 5 * 1 = 14) := by
  unfold catalanNumber
  norm_num [Nat.choose]

end Omega.POM.CatalanMoments
