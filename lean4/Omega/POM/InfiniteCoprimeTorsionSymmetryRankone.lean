import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-infinite-coprime-torsion-symmetry-rankone`. -/
theorem paper_pom_infinite_coprime_torsion_symmetry_rankone {u : ℕ → ℂ} {Q : Set ℕ}
    (hQlarge : ∀ N : ℕ, ∃ q ∈ Q, N < q)
    (hvanish : ∀ q ∈ Q, ∀ n : ℕ, 1 ≤ n → ¬ q ∣ n → u n = 0) :
    ∀ n : ℕ, 1 ≤ n → u n = 0 := by
  intro n hn
  obtain ⟨q, hqQ, hnq⟩ := hQlarge n
  exact hvanish q hqQ n hn (fun hqdiv => by
    have hqle : q ≤ n := Nat.le_of_dvd hn hqdiv
    omega)

end Omega.POM
