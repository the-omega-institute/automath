import Omega.Folding.MomentSum

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing seed wrapper for the largest-fiber zero-temperature law in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:max-fiber -/
theorem paper_projection_max_fiber (q m : Nat) :
    (Omega.X.maxFiberMultiplicity m) ^ q ≤ Omega.momentSum q m ∧
      Omega.momentSum q m ≤ Nat.fib (m + 2) * (Omega.X.maxFiberMultiplicity m) ^ q := by
  constructor
  · obtain ⟨x, hx⟩ := Omega.X.maxFiberMultiplicity_achieved m
    have hxmem : x ∈ (Finset.univ : Finset (Omega.X m)) := by simp
    rw [Omega.momentSum]
    calc
      (Omega.X.maxFiberMultiplicity m) ^ q = (Omega.X.fiberMultiplicity x) ^ q := by rw [← hx]
      _ ≤ ∑ y : Omega.X m, (Omega.X.fiberMultiplicity y) ^ q := by
        simpa using
          (Finset.single_le_sum
            (fun y _ => Nat.zero_le ((Omega.X.fiberMultiplicity y) ^ q)) hxmem :
              (Omega.X.fiberMultiplicity x) ^ q ≤
                ∑ y : Omega.X m, (Omega.X.fiberMultiplicity y) ^ q)
  · calc
      Omega.momentSum q m ≤ ∑ _y : Omega.X m, (Omega.X.maxFiberMultiplicity m) ^ q := by
        rw [Omega.momentSum]
        apply Finset.sum_le_sum
        intro y hy
        exact Nat.pow_le_pow_left (Omega.X.fiberMultiplicity_le_max y) q
      _ = Nat.fib (m + 2) * (Omega.X.maxFiberMultiplicity m) ^ q := by
        simp [Omega.X.card_eq_fib, Finset.card_univ]

end Omega.POM
