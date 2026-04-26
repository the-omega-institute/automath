import Omega.Zeta.XiTimePart64baFoldMultiplicityMajorizationBalancing

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9xaa-wulff-universal-convex-envelope`.

This Lean wrapper records the strictly convex Robin-Hood smoothing inequality used by the
Wulff balancing argument, together with the chapter-local balanced-profile certificate. -/
theorem paper_xi_time_part9xaa_wulff_universal_convex_envelope
    {F M : ℕ} (hF : 0 < F) (Φ : ℕ → ℝ)
    (hconv : ∀ a b : ℕ, a + 1 < b → Φ a + Φ b > Φ (a + 1) + Φ (b - 1))
    (d : Fin F → ℕ) (hpos : ∀ i, 1 ≤ d i) (hsum : ∑ i, d i = M) :
    let wulffProfile := xiTimePart64baBalancedProfile F M
    (∀ x y : ℕ, y + 1 < x → Φ x + Φ y > Φ (x - 1) + Φ (y + 1)) ∧
      (∀ i, wulffProfile i = M / F ∨ wulffProfile i = M / F + 1) ∧
      (∀ i j, Int.natAbs ((wulffProfile i : ℤ) - wulffProfile j) ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧
      ∑ i, d i = M := by
  have _hF : 0 < F := hF
  dsimp
  rcases paper_xi_time_part64ba_fold_multiplicity_majorization_balancing (F := F) (M := M)
    with ⟨_, hwulffValues, hwulffGap, _, _⟩
  refine ⟨?_, hwulffValues, hwulffGap, ?_, hsum⟩
  · intro x y hyx
    have hsmooth := hconv y x hyx
    nlinarith
  · intro i
    exact Nat.ne_of_gt (hpos i)

end Omega.Zeta
