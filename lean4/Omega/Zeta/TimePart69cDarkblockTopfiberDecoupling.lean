import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part69c-darkblock-topfiber-decoupling`. -/
theorem paper_xi_time_part69c_darkblock_topfiber_decoupling
    (fib zeroBlock maxFiber topNoncontractible : ℕ → ℕ) (ratio : ℕ → ℝ) (Cphi : ℝ)
    (hzero : ∀ m, m % 6 = 4 → fib ((m + 2) / 2) ≤ zeroBlock m)
    (htop : ∀ m, m % 6 = 4 → topNoncontractible m = maxFiber m)
    (hratio : ∀ m, m % 6 = 4 → 1 + Cphi ≤ ratio m) :
    ∀ m,
      m % 6 = 4 →
        fib ((m + 2) / 2) ≤ zeroBlock m ∧
          topNoncontractible m = maxFiber m ∧
            1 + Cphi ≤ ratio m := by
  intro m hm
  exact ⟨hzero m hm, htop m hm, hratio m hm⟩

end Omega.Zeta
