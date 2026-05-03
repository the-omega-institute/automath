import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Units

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62da-dirichlet-twists-intrinsic-on-fibonacci-levels`. -/
theorem paper_xi_time_part62da_dirichlet_twists_intrinsic_on_fibonacci_levels
    (N : ℕ) (χ : (ZMod N)ˣ →* ℂˣ) (_hN : 0 < N)
    (hcofinal : ∃ m ≥ 1, N ∣ Nat.fib (m + 2)) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∃ ρ : (ZMod (Nat.fib (m + 2)))ˣ →* (ZMod N)ˣ,
        ∃ χtilde : (ZMod (Nat.fib (m + 2)))ˣ →* ℂˣ, χtilde = χ.comp ρ := by
  rcases hcofinal with ⟨m, hm, hdiv⟩
  refine ⟨m, hm, ?_⟩
  let ρ : (ZMod (Nat.fib (m + 2)))ˣ →* (ZMod N)ˣ := ZMod.unitsMap hdiv
  exact ⟨ρ, χ.comp ρ, rfl⟩

end Omega.Zeta
