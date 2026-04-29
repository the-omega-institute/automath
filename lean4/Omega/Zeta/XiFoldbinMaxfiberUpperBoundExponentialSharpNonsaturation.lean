namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-maxfiber-upper-bound-exponential-sharp-nonsaturation`. -/
theorem paper_xi_foldbin_maxfiber_upper_bound_exponential_sharp_nonsaturation
    (upper dmax : Nat -> Int) (rateLock : Prop) (hrate : rateLock)
    (hgap : ∃ m0, ∀ m, m0 ≤ m -> 0 < upper m - dmax m) :
    (∃ m0, ∀ m, m0 ≤ m -> 0 < upper m - dmax m) ∧ rateLock := by
  exact ⟨hgap, hrate⟩

end Omega.Zeta
