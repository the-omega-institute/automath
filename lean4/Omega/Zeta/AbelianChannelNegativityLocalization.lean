import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-abelian-channel-negativity-localization`. -/
theorem paper_xi_abelian_channel_negativity_localization {ι : Type*} [Fintype ι]
    (neg : ι → ℕ) (hneg : 0 < Finset.univ.sum neg) : ∃ chi : ι, 0 < neg chi := by
  classical
  rcases (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := neg)
      (fun _ _ => Nat.zero_le _)).mp hneg with ⟨chi, _hchi_mem, hchi⟩
  exact ⟨chi, hchi⟩

end Omega.Zeta
