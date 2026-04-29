import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-addressable-godel-worstcase-chebyshev-sharp-lower-bound`. -/
theorem paper_xi_addressable_godel_worstcase_chebyshev_sharp_lower_bound {T q : ℕ}
    (hq : 2 ≤ q) (pLog : Fin T → ℝ) (L : (Fin T → Fin q) → ℝ)
    (mval : (t : Fin T) → Fin q → ℕ) (hpos : ∀ t, ∃ a, 1 ≤ mval t a)
    (hL : ∀ s, (∑ t, (mval t (s t) : ℝ) * pLog t) ≤ L s)
    (hnonneg : ∀ t, 0 ≤ pLog t) :
    ∃ s : Fin T → Fin q, (∑ t, pLog t) ≤ L s := by
  classical
  have _hq_pos : 0 < q := by omega
  let s : Fin T → Fin q := fun t => Classical.choose (hpos t)
  refine ⟨s, ?_⟩
  calc
    (∑ t, pLog t) ≤ ∑ t, (mval t (s t) : ℝ) * pLog t := by
      refine Finset.sum_le_sum ?_
      intro t _ht
      have hm : 1 ≤ mval t (s t) := by
        dsimp [s]
        exact Classical.choose_spec (hpos t)
      have hm_real : (1 : ℝ) ≤ (mval t (s t) : ℝ) := by exact_mod_cast hm
      have hp := hnonneg t
      nlinarith
    _ ≤ L s := hL s

end Omega.Zeta
