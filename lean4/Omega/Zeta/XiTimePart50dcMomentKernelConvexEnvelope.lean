import Omega.Zeta.XiTimePart50dcProjectivePressurePerronLogconvex

namespace Omega.Zeta

/-- `cor:xi-time-part50dc-moment-kernel-convex-envelope`.  A finite projective
pressure, being a supremum of affine path weights, is convex on every interval. -/
theorem paper_xi_time_part50dc_moment_kernel_convex_envelope
    (n : ℕ) (offset slope : Fin (n + 1) → ℝ) (q₀ q₁ θ : ℝ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    xiProjectivePressure n offset slope ((1 - θ) * q₀ + θ * q₁) ≤
      (1 - θ) * xiProjectivePressure n offset slope q₀ +
        θ * xiProjectivePressure n offset slope q₁ := by
  unfold xiProjectivePressure
  refine Finset.sup'_le (s := Finset.univ) (H := Finset.univ_nonempty)
    (f := xiAffinePathWeight offset slope ((1 - θ) * q₀ + θ * q₁)) ?_
  intro i _hi
  have hleft :
      xiAffinePathWeight offset slope q₀ i ≤
        Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₀) := by
    exact Finset.le_sup' (f := xiAffinePathWeight offset slope q₀) (Finset.mem_univ i)
  have hright :
      xiAffinePathWeight offset slope q₁ i ≤
        Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₁) := by
    exact Finset.le_sup' (f := xiAffinePathWeight offset slope q₁) (Finset.mem_univ i)
  have hweight :
      xiAffinePathWeight offset slope ((1 - θ) * q₀ + θ * q₁) i =
        (1 - θ) * xiAffinePathWeight offset slope q₀ i +
          θ * xiAffinePathWeight offset slope q₁ i := by
    unfold xiAffinePathWeight
    ring
  have hθleft : 0 ≤ 1 - θ := by
    linarith
  have hleft' :
      (1 - θ) * xiAffinePathWeight offset slope q₀ i ≤
        (1 - θ) *
          Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₀) := by
    exact mul_le_mul_of_nonneg_left hleft hθleft
  have hright' :
      θ * xiAffinePathWeight offset slope q₁ i ≤
        θ *
          Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₁) := by
    exact mul_le_mul_of_nonneg_left hright hθ₀
  linarith

end Omega.Zeta
