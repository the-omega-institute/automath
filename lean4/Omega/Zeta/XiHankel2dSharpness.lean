import Omega.Zeta.DephysHankelFiniteAudit
import Omega.Zeta.HankelWindowFiber1d

namespace Omega.Zeta

open XiHankelWindowFiber1dData

/-- Paper label: `cor:xi-hankel-2d-sharpness`.
The finite-audit theorem gives deterministic recovery from `2d` samples, while the canonical
one-parameter family already contains distinct rank-`d` sequences sharing the shifted
length-`2d-1` window indexed by `1, …, 2d - 1`. -/
theorem paper_xi_hankel_2d_sharpness
    {k : Type*} [Field k] (D : XiHankelWindowFiber1dData k) :
    (∀ a b : ℕ → k,
      (∀ n : ℕ, n < 2 * D.d → a n = b n) →
        hankelPrincipal a D.d = hankelPrincipal b D.d ∧ hankelShift a D.d = hankelShift b D.d) ∧
    ∃ a b : ℕ → k,
      a ≠ b ∧ D.hankelRankEqD a ∧ D.hankelRankEqD b ∧
        (∀ n : ℕ, n < 2 * D.d - 1 → a (n + 1) = b (n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro a b hwindow
    exact dephys_hankel_finite_audit_window_determines_hankel_blocks a b D.d hwindow
  · refine ⟨D.canonicalSequence 0, D.canonicalSequence 1, ?_, D.hankelRankEqD_canonical 0,
      D.hankelRankEqD_canonical 1, ?_⟩
    · intro hEq
      have h0 := congrArg (fun f : ℕ → k => f 0) hEq
      simp [canonicalSequence] at h0
    · intro n hn
      simp [canonicalSequence]

end Omega.Zeta
