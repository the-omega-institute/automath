import Omega.POM.ToggleOrbitCountBellProduct

namespace Omega.POM

lemma truncatedBell_two_eq_two (n : ℕ) (hn : 2 ≤ n) : truncatedBell 2 n = 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero =>
      native_decide
  | succ m ih =>
      rw [truncatedBell, Finset.sum_range_succ]
      have hz : Nat.stirlingSecond 2 (m + 3) = 0 := Nat.stirlingSecond_eq_zero_of_lt (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, truncatedBell, hz] using ih

/-- Paper label: `cor:pom-toggle-orbit-count-commutant-identity`.
For components of size at least `2`, each `q = 2` truncated Bell factor equals `2`, so the
diagonal toggle-orbit count is exactly `2^r`, where `r` is the number of components. -/
theorem paper_pom_toggle_orbit_count_commutant_identity (componentSizes : List Nat)
    (hcomp : ∀ n ∈ componentSizes, 2 ≤ n) :
    Omega.POM.toggleOrbitCount componentSizes 2 = 2 ^ componentSizes.length := by
  induction componentSizes with
  | nil =>
      simp [toggleOrbitCount]
  | cons n ns ih =>
      have hn : 2 ≤ n := hcomp n (by simp)
      have hns : ∀ m ∈ ns, 2 ≤ m := by
        intro m hm
        exact hcomp m (by simp [hm])
      rw [toggleOrbitCount_cons, truncatedBell_two_eq_two n hn, ih hns]
      change 2 * 2 ^ ns.length = 2 ^ (ns.length + 1)
      rw [pow_succ, Nat.mul_comm]

end Omega.POM
